module

public import KVApproximation.Dynamics.PronyModel
public import KVApproximation.Dynamics.TrajectoryBounds

/-!
# Finite Prony sums and memory convolution
-/

public section

open MeasureTheory

namespace KVApproximation.Dynamics

variable {M E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Proposition B.10 (`eq:q_i_duhamel`, `eq:Kn_def`): summing the
internal-state convolutions is exactly convolution with the finite Prony kernel. -/
theorem pronyStress_eq_kernel_convolution {n : ℕ} (P : PronyModel M E n)
    (a : M) (e : BoundedTrajectory E) {t : ℝ} (ht : 0 ≤ t) :
    P.stress a e t = P.viscosity a (e.velocity t) + P.elasticity a (e.value t) +
      ∫ s in (0 : ℝ)..t, P.kernel a (t - s) (e.velocity s) := by
  have hi (k : Fin n) : IntervalIntegrable (fun s =>
      Real.exp (-P.rate k * (t - s)) • P.coefficient k a (e.velocity s)) volume 0 t := by
    have hv : IntervalIntegrable (fun s => P.coefficient k a (e.velocity s)) volume 0 t :=
      ⟨(P.coefficient k a).integrable_comp (e.velocity_intervalIntegrable le_rfl ht).1,
        (P.coefficient k a).integrable_comp (e.velocity_intervalIntegrable le_rfl ht).2⟩
    exact hv.continuousOn_smul (by fun_prop)
  unfold PronyModel.stress PronyModel.stressResponse PronyModel.state
  congr 1
  change (∑ k : Fin n, ∫ s in (0 : ℝ)..t,
    Real.exp (-P.rate k * (t - s)) • P.coefficient k a (e.velocity s)) = _
  rw [← intervalIntegral.integral_finsetSum (fun k _ => hi k)]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [PronyModel.kernel, sum_apply, smul_apply]

end KVApproximation.Dynamics
