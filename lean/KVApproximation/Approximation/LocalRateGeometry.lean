import KVApproximation.Approximation.LocalResponse
import KVApproximation.Approximation.LogPartitionIdentities
import KVApproximation.Approximation.BernsteinGeometry
import KVApproximation.Approximation.EllipseConstant

/-!
# Local rate maps on the radius-two ellipse
-/

namespace KVApproximation.Approximation

/-- Lemma B.9: the complex rate map extends the real change of variables. -/
theorem complexLocalRate_ofReal (lower R : ℝ)
    (j : Fin (logPartitionCount R)) (x : ℝ) :
    complexLocalRate lower R j x = (localRate lower R j x : ℂ) := by
  simp only [complexLocalRate, localRate, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_add]

/-- Lemma B.9: the radius-two ellipse maps into the open right half-plane,
with the exact secant bound used in the paper. -/
theorem complexLocalRate_ellipse {lower R : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R)) {z : ℂ} (hz : z ∈ bernsteinEllipse 2) :
    0 < (complexLocalRate lower R j z).re ∧
      ‖complexLocalRate lower R j z‖ / (complexLocalRate lower R j z).re ≤
        (Real.cos (3 / 4))⁻¹ := by
  let a := (logPatchLeft R j + logPatchRight R j) / 2
  let b := (logPatchRight R j - logPatchLeft R j) / 2
  have hbpos : 0 < b := div_pos (logPatch_width hR j).1 (by norm_num)
  have hb1 : b ≤ 1 := (logPatch_width hR j).2
  have hzIm : |z.im| ≤ (3 : ℝ) / 4 := by
    simpa only [bernsteinImaginarySemiaxis_two] using
      bernsteinEllipse_im_le (by norm_num : (1 : ℝ) < 2) hz
  have hangle : |b * z.im| ≤ (3 : ℝ) / 4 := by
    rw [abs_mul, abs_of_pos hbpos]
    simpa only [one_mul] using mul_le_mul hb1 hzIm (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hcoslower : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
  have hcos : Real.cos (3 / 4 : ℝ) ≤ Real.cos (b * z.im) := by
    rw [← Real.cos_abs (b * z.im)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three]) hangle
  have hcospos := hcoslower.trans_le hcos
  have hp : 0 < lower * Real.exp (a + b * z.re) := mul_pos hlower (Real.exp_pos _)
  have hre : (complexLocalRate lower R j z).re =
      lower * Real.exp (a + b * z.re) * Real.cos (b * z.im) := by
    change ((lower : ℂ) * Complex.exp ((a : ℂ) + (b : ℂ) * z)).re = _
    simp only [Complex.mul_re, Complex.exp_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, zero_add, add_zero]
    ring
  have hnorm : ‖complexLocalRate lower R j z‖ = lower * Real.exp (a + b * z.re) := by
    change ‖(lower : ℂ) * Complex.exp ((a : ℂ) + (b : ℂ) * z)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlower, Complex.norm_exp]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  constructor
  · rw [hre]
    exact mul_pos hp hcospos
  · rw [hnorm, hre]
    calc
      _ = (Real.cos (b * z.im))⁻¹ := by field_simp
      _ ≤ (Real.cos (3 / 4))⁻¹ := (inv_le_inv₀ hcospos hcoslower).mpr hcos

end KVApproximation.Approximation
