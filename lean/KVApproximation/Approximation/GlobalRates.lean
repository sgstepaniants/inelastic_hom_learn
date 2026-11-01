module

public import KVApproximation.Approximation.AlternativeProny

/-!
# Shared rates for global logarithmic interpolation
-/

public section

namespace KVApproximation.Approximation

/-- Remark 4.6: every global reference node gives a rate in the common
spectral interval, including a singleton interval. -/
theorem globalLogRate_mem {lower upper x : ℝ} (hlower : 0 < lower)
    (horder : lower ≤ upper) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    globalLogRate lower upper x ∈ Set.Icc lower upper := by
  have hR : 0 ≤ logarithmicSpan lower upper :=
    Real.log_nonneg ((one_le_div hlower).mpr horder)
  have hleft : 0 ≤ logarithmicSpan lower upper / 2 * (1 + x) :=
    mul_nonneg (div_nonneg hR (by norm_num)) (by linarith [hx.1])
  have hright : logarithmicSpan lower upper / 2 * (1 + x) ≤
      logarithmicSpan lower upper := by
    nlinarith [mul_nonneg hR (show 0 ≤ 1 - x by linarith [hx.2])]
  constructor
  · calc
      lower = lower * Real.exp 0 := by simp
      _ ≤ globalLogRate lower upper x :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hleft) hlower.le
  · calc
      globalLogRate lower upper x ≤ lower * Real.exp (logarithmicSpan lower upper) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hright) hlower.le
      _ = upper := by
        rw [logarithmicSpan, Real.exp_log (div_pos (hlower.trans_le horder) hlower),
          mul_div_cancel₀ _ hlower.ne']

end KVApproximation.Approximation
