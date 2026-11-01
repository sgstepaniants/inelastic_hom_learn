module

public import KVApproximation.Analysis.AnnulusCoefficients
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic.FieldSimp

/-!
# Circle integrals and symmetric Fourier coefficients
-/

public section

namespace KVApproximation.Analysis

open MeasureTheory

local instance circleFourierPeriodPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Lemma B.9, analytic coefficient proof: the unit-radius Laurent
coefficient is the corresponding Fourier coefficient of the circle pullback. -/
theorem circleCoefficient_eq_fourierCoeff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (k : ℕ) :
    circleCoefficient f 1 k = fourierCoeff
      (fun t : AddCircle (2 * Real.pi) => f (t.toCircle : ℂ)) (k : ℤ) := by
  rw [circleCoefficient, fourierCoeff_eq_intervalIntegral _ _ 0, circleIntegral]
  simp only [zero_add]
  rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  have hcircle : (AddCircle.toCircle (θ : AddCircle (2 * Real.pi)) : ℂ) = circleMap 0 1 θ := by
    simp only [AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul,
      Circle.coe_exp, circleMap, zero_add, Complex.ofReal_one]
  have hfourier : fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) =
      ((circleMap 0 1 θ) ^ k)⁻¹ := by
    simp only [fourier_apply, AddCircle.toCircle_zsmul,
      zpow_neg, zpow_natCast, Circle.coe_inv, Circle.coe_pow, hcircle]
  rw [hfourier, hcircle, deriv_circleMap, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_smul]
  congr 1
  have hz : circleMap 0 1 θ ≠ 0 := by
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
    exact Complex.exp_ne_zero _
  rw [pow_succ]
  push_cast
  field_simp
  rfl

/-- Lemma B.9, analytic coefficient proof: an even circle function has
equal opposite Fourier coefficients, also for complex-valued functions. -/
theorem fourierCoeff_neg_of_even
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : ℝ} [Fact (0 < T)] {f : AddCircle T → F}
    (hf : ∀ t, f (-t) = f t) (k : ℤ) :
    fourierCoeff f (-k) = fourierCoeff f k := by
  unfold fourierCoeff
  simp only [neg_neg]
  calc
    (∫ t : AddCircle T, fourier k t • f t ∂AddCircle.haarAddCircle) =
        ∫ t : AddCircle T, fourier (-k) (-t) • f (-t) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [hf, fourier_apply, neg_smul, smul_neg, neg_neg]
    _ = _ := integral_neg_eq_self (fun t : AddCircle T => fourier (-k) t • f t) AddCircle.haarAddCircle

end KVApproximation.Analysis
