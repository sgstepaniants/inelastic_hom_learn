module

public import KVApproximation.Analysis.HalfLineLaplaceUniqueness

/-!
# Laplace uniqueness under an exponential bound

Damping reduces continuous trajectories of exponential growth to the bounded
case. Multiplication by a real exponential shifts the Laplace parameter.
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Theorem 3.1, damped residual: exponential multiplication shifts
the real Laplace parameter by the damping rate. -/
theorem halfLineLaplace_exp_smul (u : ℝ → F) (a s : ℝ) :
    halfLineLaplace (fun t => Real.exp (-a * t) • u t) s =
      halfLineLaplace u (s + a) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change Real.exp (-s * t) • (Real.exp (-a * t) • u t) =
      Real.exp (-(s + a) * t) • u t
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring

/-- Theorem 3.1, time-domain recovery: a continuous trajectory with
a bounded exponential damping is determined by transforms beyond that rate. -/
theorem eq_zero_of_halfLineLaplace_eq_zero_of_damped_bound [CompleteSpace F]
    (u : ℝ → F) (hu : ContinuousOn u (Set.Ici (0 : ℝ))) (a : ℝ) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖Real.exp (-a * t) • u t‖ ≤ M)
    (hLap : ∀ s : ℝ, a < s → halfLineLaplace u s = 0) :
    ∀ t : ℝ, 0 ≤ t → u t = 0 := by
  let v : ℝ → F := fun t => Real.exp (-a * t) • u t
  have hv : ContinuousOn v (Set.Ici (0 : ℝ)) :=
    (show Continuous (fun t : ℝ => Real.exp (-a * t)) from by fun_prop).continuousOn.smul hu
  have heq : Set.EqOn v (fun _ => (0 : F)) (Set.Ici (0 : ℝ)) := by
    apply eqOn_of_halfLineLaplace_eq v (fun _ => (0 : F)) hv continuousOn_const
      hbound (Mv := 0) (fun _ _ => by simp)
    intro s hs
    rw [show halfLineLaplace v s = halfLineLaplace u (s + a) from
      halfLineLaplace_exp_smul u a s, hLap (s + a) (by linarith)]
    simp [halfLineLaplace]
  intro t ht
  have hz : Real.exp (-a * t) • u t = 0 := heq ht
  exact (smul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

end KVApproximation.Analysis
