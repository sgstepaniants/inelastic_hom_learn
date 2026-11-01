import KVApproximation.Approximation.GlobalResponse
import KVApproximation.Approximation.BernsteinGeometry
import KVApproximation.Approximation.EllipseConstant

/-!
# The global rate map on a span-dependent ellipse
-/

namespace KVApproximation.Approximation

/-- Remark 4.6: the complex global rate restricts to the real rate. -/
theorem complexGlobalLogRate_ofReal (lower upper x : ℝ) :
    complexGlobalLogRate lower upper x = (globalLogRate lower upper x : ℂ) := by
  simp only [complexGlobalLogRate, globalLogRate, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_add, Complex.ofReal_one]

/-- Remark 4.6: the ellipse of parameter `1 + 1/R` keeps the global rate
in the same right-half-plane sector used for local interpolation. -/
theorem complexGlobalLogRate_ellipse_of_span_pos {lower upper : ℝ} (hlower : 0 < lower)
    (hR : 0 < logarithmicSpan lower upper) {z : ℂ}
    (hz : z ∈ bernsteinEllipse (1 + 1 / logarithmicSpan lower upper)) :
    0 < (complexGlobalLogRate lower upper z).re ∧
      ‖complexGlobalLogRate lower upper z‖ / (complexGlobalLogRate lower upper z).re ≤
        (Real.cos (3 / 4))⁻¹ := by
  let R := logarithmicSpan lower upper
  let b := R / 2
  have hRpos : 0 < R := hR
  have hb : 0 < b := div_pos hRpos (by norm_num)
  have hρ : 1 < 1 + 1 / R := by linarith [one_div_pos.mpr hRpos]
  have haxis : b * bernsteinImaginarySemiaxis (1 + 1 / R) ≤ (1 : ℝ) / 2 := by
    have heq : b * bernsteinImaginarySemiaxis (1 + 1 / R) = (2 * R + 1) / (4 * (R + 1)) := by
      dsimp [b, bernsteinImaginarySemiaxis]
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (R + 1))).mpr
    linarith
  have hangle : |b * z.im| ≤ (3 : ℝ) / 4 := by
    rw [abs_mul, abs_of_pos hb]
    have h := mul_le_mul_of_nonneg_left (bernsteinEllipse_im_le hρ hz) hb.le
    linarith
  have hcoslower : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
  have hcos : Real.cos (3 / 4 : ℝ) ≤ Real.cos (b * z.im) := by
    rw [← Real.cos_abs (b * z.im)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three]) hangle
  have hcospos := hcoslower.trans_le hcos
  have hp : 0 < lower * Real.exp (b * (1 + z.re)) := mul_pos hlower (Real.exp_pos _)
  have hre : (complexGlobalLogRate lower upper z).re =
      lower * Real.exp (b * (1 + z.re)) * Real.cos (b * z.im) := by
    change ((lower : ℂ) * Complex.exp ((b : ℂ) * (1 + z))).re = _
    simp only [Complex.mul_re, Complex.exp_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      zero_mul, sub_zero, zero_add, add_zero]
    ring
  have hnorm : ‖complexGlobalLogRate lower upper z‖ = lower * Real.exp (b * (1 + z.re)) := by
    change ‖(lower : ℂ) * Complex.exp ((b : ℂ) * (1 + z))‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlower, Complex.norm_exp]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, zero_mul, sub_zero]
  constructor
  · rw [hre]
    exact mul_pos hp hcospos
  · rw [hnorm, hre]
    calc
      _ = (Real.cos (b * z.im))⁻¹ := by field_simp
      _ ≤ (Real.cos (3 / 4))⁻¹ := (inv_le_inv₀ hcospos hcoslower).mpr hcos

/-- Remark 4.6: the ellipse of parameter `1 + 1/R` keeps the global rate
in the same right-half-plane sector used for local interpolation. -/
theorem complexGlobalLogRate_ellipse {lower upper : ℝ} (hlower : 0 < lower)
    (hR : 1 ≤ logarithmicSpan lower upper) {z : ℂ}
    (hz : z ∈ bernsteinEllipse (1 + 1 / logarithmicSpan lower upper)) :
    0 < (complexGlobalLogRate lower upper z).re ∧
      ‖complexGlobalLogRate lower upper z‖ / (complexGlobalLogRate lower upper z).re ≤
        (Real.cos (3 / 4))⁻¹ := by
  exact complexGlobalLogRate_ellipse_of_span_pos hlower (lt_of_lt_of_le zero_lt_one hR) hz

end KVApproximation.Approximation
