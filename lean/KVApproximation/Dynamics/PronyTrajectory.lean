module

public import KVApproximation.Dynamics.PronyModel
public import KVApproximation.Dynamics.DampedResponseProperties
public import KVApproximation.Dynamics.TrajectoryBounds
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Bounded Sobolev trajectories of the Prony states
-/

public section

open MeasureTheory

namespace KVApproximation.Dynamics

variable {M E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Proposition B.10 (`eq:q_i_ode`, `eq:q_i_duhamel`): the convolution
state has bounded value and velocity and solves the Prony initial-value problem. -/
theorem pronyState_isKineticSolution {n : ℕ} (P : PronyModel M E n)
    (hRate : ∀ k, 0 < P.rate k) (a : M) (e : BoundedTrajectory E) :
    ∃ q : BoundedTrajectory (BlockState n E),
      (∀ t : ℝ, 0 ≤ t → q.value t = P.state a e t) ∧
      IsKineticSolution e (fun vq => P.kineticResponse a vq.1 vq.2) q := by
  classical
  have hforcing (k : Fin n) : MemLp (fun t => P.coefficient k a (e.velocity t))
      ⊤ timeMeasure := e.velocity_memLp.continuousLinearMap_comp (P.coefficient k a)
  choose q hvalue hzero hvelocity using fun k : Fin n =>
    dampedResponse_trajectory (hRate k) _ (hforcing k)
  let Q : BoundedTrajectory (BlockState n E) := {
    value := fun t => WithLp.toLp 2 (fun k => (q k).value t)
    velocity := fun t => WithLp.toLp 2 (fun k => (q k).velocity t)
    value_memLp := memLp_piLp_iff.mpr (fun k => (q k).value_memLp)
    velocity_memLp := memLp_piLp_iff.mpr (fun k => (q k).velocity_memLp)
    integral_eq := by
      intro t ht
      apply PiLp.ext
      intro k
      change (q k).value t = (q k).value 0 +
        (∫ s in (0 : ℝ)..t, WithLp.toLp 2 (fun j => (q j).velocity s)) k
      rw [intervalIntegral.integral_of_le ht]
      have heval := eval_integral_piLp
        (f := fun s => WithLp.toLp 2 (fun j => (q j).velocity s))
        (fun j => ((q j).velocity_intervalIntegrable le_rfl ht).1) k
      rw [heval, ← intervalIntegral.integral_of_le ht]
      exact (q k).integral_eq t ht
  }
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro t ht
    apply PiLp.ext
    intro k
    exact hvalue k t ht
  · apply PiLp.ext
    intro k
    exact hzero k
  · have hvel : ∀ᵐ t ∂timeMeasure, ∀ k, (q k).velocity t =
        P.coefficient k a (e.velocity t) - P.rate k • (q k).value t :=
      ae_all_iff.mpr hvelocity
    filter_upwards [hvel] with t ht
    apply PiLp.ext
    intro k
    exact ht k

end KVApproximation.Dynamics
