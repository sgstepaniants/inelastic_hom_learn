module

public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Measurable-time integral equations on a half-line
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace KVApproximation.Dynamics

/-- Proposition B.13, global Carathéodory ingredient: compatible finite
interval solutions give a continuous integral solution on the half-line.
No uniform bound on its state is assumed or asserted here. -/
theorem exists_integral_solution_Ici {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} {a : ℝ} {K : ℝ≥0}
    (hLip : ∀ᵐ s ∂volume.restrict (Ici a), LipschitzWith K (f s))
    (hInt : ∀ b : ℝ, a ≤ b → ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b)) (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Ici a) ∧ x a = x₀ ∧
      ∀ t ∈ Ici a, x t = x₀ + ∫ s in a..t, f s (x s) := by
  sorry

end KVApproximation.Dynamics
