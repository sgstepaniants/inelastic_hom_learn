module

public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Measurable-time nonlinear integral equations
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace KVApproximation.Dynamics

/-- Proposition B.13, Carathéodory existence ingredient: a uniformly
Lipschitz field with integrable evaluations along continuous curves has
an integral solution on every finite interval in a complete Banach space. -/
theorem exists_integral_solution_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} {a b : ℝ} {K : ℝ≥0}
    (hLip : ∀ᵐ s ∂volume.restrict (Icc a b), LipschitzWith K (f s))
    (hInt : ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b)) (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Icc a b) ∧ x a = x₀ ∧
      ∀ t ∈ Icc a b, x t = x₀ + ∫ s in a..t, f s (x s) := by
  sorry

/-- Proposition B.13, Carathéodory uniqueness ingredient: two continuous
integral solutions with the same initial value agree on the interval.
Completeness is needed for existence, but not for uniqueness. -/
theorem integral_solution_unique_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E → E} {a b : ℝ} {K : ℝ≥0}
    (hLip : ∀ᵐ s ∂volume.restrict (Icc a b), LipschitzWith K (f s))
    (hInt : ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b))
    {x₀ : E} {x₁ x₂ : ℝ → E}
    (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = x₀ + ∫ s in a..t, f s (x₁ s))
    (h₂ : ∀ t ∈ Icc a b, x₂ t = x₀ + ∫ s in a..t, f s (x₂ s)) :
    EqOn x₁ x₂ (Icc a b) := by
  sorry

end KVApproximation.Dynamics
