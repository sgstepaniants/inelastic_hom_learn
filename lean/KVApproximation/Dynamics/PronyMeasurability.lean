module

public import KVApproximation.Dynamics.PronyModel
public import KVApproximation.Dynamics.DampedResponseProperties
public import KVApproximation.Dynamics.TrajectoryBounds

/-!
# Measurability of finite Prony stresses
-/

public section

open MeasureTheory

namespace KVApproximation.Dynamics

/-- Proposition B.10: the finite Prony stress is measurable even when
the strain velocity is only almost-everywhere measurable. -/
theorem aestronglyMeasurable_pronyStress {M E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (P : PronyModel M E n) (a : M) (e : BoundedTrajectory E) :
    AEStronglyMeasurable (P.stress a e) timeMeasure := by
  have hq (k : Fin n) : ContinuousOn (fun t => P.state a e t k) (Set.Ici 0) := by
    apply continuousOn_dampedResponse
    intro t ht
    have hv := e.velocity_intervalIntegrable le_rfl ht
    exact ⟨(P.coefficient k a).integrable_comp hv.1,
      (P.coefficient k a).integrable_comp hv.2⟩
  have hs : AEStronglyMeasurable (fun t => ∑ k : Fin n, P.state a e t k) timeMeasure :=
    Finset.aestronglyMeasurable_fun_sum _
      (fun k _ => (hq k).aestronglyMeasurable measurableSet_Ici)
  exact ((P.viscosity a).continuous.comp_aestronglyMeasurable
    e.velocity_memLp.aestronglyMeasurable).add
    ((P.elasticity a).continuous.comp_aestronglyMeasurable e.value_memLp.aestronglyMeasurable)
    |>.add hs

end KVApproximation.Dynamics
