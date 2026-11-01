module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integration by parts with a varying bounded operator
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Appendix A.3, Duhamel integrability: a continuous operator curve
applied to an integrable vector field remains integrable. -/
theorem intervalIntegrable_continuous_clm_apply {a b : ℝ}
    {Φ : ℝ → E →L[ℝ] F} {f : ℝ → E}
    (hΦ : ContinuousOn Φ (Set.uIcc a b)) (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => Φ t (f t)) volume a b := by
  sorry

/-- Appendix A.3 (`eq:eta_sol`), integration by parts: a continuously
differentiable operator pairs with the primitive of an integrable field. -/
theorem integral_deriv_clm_primitive_eq_sub_of_le [CompleteSpace E] [CompleteSpace F]
    {a b : ℝ} {Φ : ℝ → E →L[ℝ] F} {f : ℝ → E} (hab : a ≤ b)
    (hΦ : ContDiff ℝ 1 Φ) (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, (deriv Φ t) (∫ s in a..t, f s)) =
      Φ b (∫ s in a..b, f s) - ∫ t in a..b, Φ t (f t) := by
  sorry

end KVApproximation.Analysis
