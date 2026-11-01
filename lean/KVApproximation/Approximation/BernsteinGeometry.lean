module

public import KVApproximation.Analysis.Joukowski
public import KVApproximation.Approximation.Interpolation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# The Joukowski map and Bernstein ellipses
-/

public section

namespace KVApproximation

/-- Lemma B.9, analytic coefficient proof: inversion preserves the Joukowski map. -/
theorem Analysis.joukowski_inv (w : ℂ) :
    joukowski w⁻¹ = joukowski w := by
  simp only [joukowski, inv_inv, add_comm]

/-- Lemma B.9, analytic coefficient proof: the unit circle maps to its real part. -/
theorem Analysis.joukowski_unit {w : ℂ} (hw : ‖w‖ = 1) :
    joukowski w = (w.re : ℂ) := by
  have hsq : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw, one_pow]
  rw [joukowski, Complex.inv_def, hsq]
  simp only [Complex.ofReal_one, inv_one, mul_one, Complex.add_conj]
  norm_cast
  ring

namespace Approximation

/-- Lemma B.9, ellipse geometry: the real semiaxis is at least one. -/
private theorem real_semiaxis_ge_one {r : ℝ} (hr : 0 < r) :
    1 ≤ (r + r⁻¹) / 2 := by
  have hid : r + r⁻¹ - 2 = (r - 1) ^ 2 / r := by field_simp; ring
  have hnonneg := div_nonneg (sq_nonneg (r - 1)) hr.le
  linarith

/-- Lemma B.9, ellipse geometry: the imaginary semiaxis is positive. -/
private theorem imaginary_semiaxis_pos {ρ : ℝ} (hρ : 1 < ρ) :
    0 < bernsteinImaginarySemiaxis ρ := by
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  have hi : ρ⁻¹ < 1 := (inv_lt_one₀ hρpos).mpr hρ
  unfold bernsteinImaginarySemiaxis
  linarith

/-- Lemma B.9, ellipse geometry: both semiaxes increase with radius above one. -/
private theorem semiaxes_mono {r ρ : ℝ} (hr : 1 ≤ r) (hrρ : r ≤ ρ) :
    (r + r⁻¹) / 2 ≤ (ρ + ρ⁻¹) / 2 ∧
      (r - r⁻¹) / 2 ≤ (ρ - ρ⁻¹) / 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hρpos : 0 < ρ := hrpos.trans_le hrρ
  have hid : ρ + ρ⁻¹ - (r + r⁻¹) = (ρ - r) * (r * ρ - 1) / (r * ρ) := by
    field_simp
    ring
  have hprod : 0 ≤ (ρ - r) * (r * ρ - 1) := by
    apply mul_nonneg (sub_nonneg.mpr hrρ)
    nlinarith
  have hnonneg := div_nonneg hprod (mul_pos hrpos hρpos).le
  have hinv : ρ⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hρpos hrpos).mpr hrρ
  constructor <;> linarith

/-- Lemma B.9, analytic coefficient proof: the outer half of the annulus
maps into the filled ellipse. -/
private theorem joukowski_outer_mem {ρ : ℝ} (hρ : 1 < ρ)
    {w : ℂ} (hw : 1 ≤ ‖w‖ ∧ ‖w‖ ≤ ρ) :
    Analysis.joukowski w ∈ bernsteinEllipse ρ := by
  let r := ‖w‖
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hw.1
  have ha : 0 < (ρ + ρ⁻¹) / 2 :=
    lt_of_lt_of_le zero_lt_one (real_semiaxis_ge_one (hr.trans_le hw.2))
  have hb := imaginary_semiaxis_pos hρ
  have har : 0 ≤ (r + r⁻¹) / 2 := (real_semiaxis_ge_one hr).trans' zero_le_one
  have hbr : 0 ≤ (r - r⁻¹) / 2 := by
    have hi : r⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr hw.1
    linarith [hw.1]
  have hmono := semiaxes_mono hw.1 hw.2
  have hratioa : ((r + r⁻¹) / 2 / ((ρ + ρ⁻¹) / 2)) ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (div_nonneg har ha.le) zero_le_one).mpr
      ((div_le_one ha).mpr hmono.1)
  have hratiob : ((r - r⁻¹) / 2 / bernsteinImaginarySemiaxis ρ) ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (div_nonneg hbr hb.le) zero_le_one).mpr
      ((div_le_one hb).mpr hmono.2)
  have hre : (Analysis.joukowski w).re = (r + r⁻¹) / 2 * (w.re / r) := by
    change ((w + w⁻¹) / ((2 : ℝ) : ℂ)).re = _
    rw [Complex.div_ofReal_re, Complex.add_re, Complex.inv_re, Complex.normSq_eq_norm_sq]
    change (w.re + w.re / r ^ 2) / 2 = _
    field_simp
  have him : (Analysis.joukowski w).im = (r - r⁻¹) / 2 * (w.im / r) := by
    change ((w + w⁻¹) / ((2 : ℝ) : ℂ)).im = _
    rw [Complex.div_ofReal_im, Complex.add_im, Complex.inv_im, Complex.normSq_eq_norm_sq]
    change (w.im + -w.im / r ^ 2) / 2 = _
    field_simp
    ring
  have hunit : (w.re / r) ^ 2 + (w.im / r) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div]
    have hsq : w.re ^ 2 + w.im ^ 2 = r ^ 2 := by
      dsimp only [r]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hsq, div_self (pow_ne_zero 2 hr.ne')]
  have ha' : ((Analysis.joukowski w).re / ((ρ + ρ⁻¹) / 2)) ^ 2 ≤ (w.re / r) ^ 2 := by
    rw [hre]
    calc
      _ = ((r + r⁻¹) / 2 / ((ρ + ρ⁻¹) / 2)) ^ 2 * (w.re / r) ^ 2 := by ring
      _ ≤ (w.re / r) ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right hratioa (sq_nonneg (w.re / r))
  have hb' : ((Analysis.joukowski w).im / bernsteinImaginarySemiaxis ρ) ^ 2 ≤ (w.im / r) ^ 2 := by
    rw [him]
    calc
      _ = ((r - r⁻¹) / 2 / bernsteinImaginarySemiaxis ρ) ^ 2 * (w.im / r) ^ 2 := by ring
      _ ≤ (w.im / r) ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right hratiob (sq_nonneg (w.im / r))
  exact (add_le_add ha' hb').trans_eq hunit

/-- Lemma B.9, analytic coefficient proof: the closed symmetric annulus
maps into the filled Bernstein ellipse. -/
theorem joukowski_mem_bernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ)
    {w : ℂ} (hw : ρ⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ ρ) :
    Analysis.joukowski w ∈ bernsteinEllipse ρ := by
  by_cases hwone : 1 ≤ ‖w‖
  · exact joukowski_outer_mem hρ ⟨hwone, hw.2⟩
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  have hwpos : 0 < ‖w‖ := (inv_pos.mpr hρpos).trans_le hw.1
  have hinv : 1 ≤ ‖w⁻¹‖ ∧ ‖w⁻¹‖ ≤ ρ := by
    rw [norm_inv]
    exact ⟨(one_le_inv₀ hwpos).mpr (le_of_not_ge hwone),
      by simpa only [inv_inv] using (inv_le_inv₀ hwpos (inv_pos.mpr hρpos)).mpr hw.1⟩
  simpa only [Analysis.joukowski_inv] using joukowski_outer_mem hρ hinv

/-- Lemma B.9: the reference interval lies in every nondegenerate Bernstein ellipse. -/
theorem real_mem_bernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (x : ℂ) ∈ bernsteinEllipse ρ := by
  have ha := real_semiaxis_ge_one (lt_trans zero_lt_one hρ)
  have hapos : 0 < (ρ + ρ⁻¹) / 2 := lt_of_lt_of_le zero_lt_one ha
  change (x / ((ρ + ρ⁻¹) / 2)) ^ 2 + (0 / bernsteinImaginarySemiaxis ρ) ^ 2 ≤ 1
  simp only [zero_div, zero_pow (by decide : 2 ≠ 0), add_zero]
  apply (sq_le_one_iff_abs_le_one _).mpr
  rw [abs_div, abs_of_pos hapos]
  exact (div_le_one hapos).mpr ((abs_le.mpr hx).trans ha)

/-- Lemma B.9: the ellipse's imaginary coordinate is bounded by its semiaxis. -/
theorem bernsteinEllipse_im_le {ρ : ℝ} (hρ : 1 < ρ)
    {z : ℂ} (hz : z ∈ bernsteinEllipse ρ) :
    |z.im| ≤ bernsteinImaginarySemiaxis ρ := by
  have hb := imaginary_semiaxis_pos hρ
  have hsq : (z.im / bernsteinImaginarySemiaxis ρ) ^ 2 ≤ 1 :=
    (le_add_of_nonneg_left (sq_nonneg _)).trans hz
  have h := (sq_le_one_iff_abs_le_one _).mp hsq
  rw [abs_div, abs_of_pos hb] at h
  exact (div_le_one hb).mp h

end Approximation
end KVApproximation
