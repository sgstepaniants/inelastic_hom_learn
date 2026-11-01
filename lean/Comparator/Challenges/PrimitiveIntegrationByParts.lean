module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.7, integration-by-parts argument: a continuously differentiable
scalar function pairs with the primitive of a merely integrable vector field.
This includes complex scalar functions and arbitrary complete Banach targets. -/
theorem integral_deriv_smul_primitive_eq_sub_of_le
    {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] [CompleteSpace F]
    {φ : ℝ → 𝕜} {f : ℝ → F} {a b : ℝ} (hab : a ≤ b)
    (hφ : ContDiff ℝ 1 φ) (hf : IntervalIntegrable f volume a b) :
    ∫ t in a..b, deriv φ t • ∫ s in a..t, f s =
      φ b • (∫ s in a..b, f s) - ∫ t in a..b, φ t • f t := by
  sorry

end KVApproximation.Analysis
