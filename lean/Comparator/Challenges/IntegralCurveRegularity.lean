module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Regularity of integral curves with bounded velocity
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace KVApproximation.Dynamics

/-- Proposition B.13, integral-to-differential bridge: an integral curve
with an essentially bounded integrable velocity is absolutely continuous
and has that velocity as its derivative almost everywhere. -/
theorem integral_curve_regularity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {q v : ℝ → E} {a b : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hv : IntervalIntegrable v volume a b)
    (hK : ∀ᵐ s ∂volume.restrict (Icc a b), ‖v s‖ ≤ K)
    (hq : ∀ t ∈ Icc a b, q t = q a + ∫ s in a..t, v s) :
    AbsolutelyContinuousOnInterval q a b ∧
      ∀ᵐ s ∂volume.restrict (Icc a b), HasDerivAt q (v s) s := by
  sorry

end KVApproximation.Dynamics
