module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp

/-!
# Finite-time bounds for exponential convolutions
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.7: integration of the positive exponential majorant. -/
private theorem integral_exponential_kernel {r t : ℝ} (hr : 0 < r) :
    (∫ s in (0 : ℝ)..t, Real.exp (-r * (t - s))) = (1 - Real.exp (-r * t)) / r := by
  have hd (s : ℝ) : HasDerivAt (fun s => Real.exp (-r * (t - s)) / r)
      (Real.exp (-r * (t - s))) s := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, neg_mul_neg, mul_one,
      mul_div_cancel_right₀ _ hr.ne'] using
      ((((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-r)).exp.div_const r)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (Continuous.intervalIntegrable (by fun_prop) 0 t)]
  simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
  ring

/-- Lemma B.7, exponential-kernel estimate: the norm of the finite-time
convolution retains the factor `1 - exp(-Re(z) * t)`. -/
theorem norm_exponential_integral_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (f : ℝ → F) {M t : ℝ} {z : ℂ} (ht : 0 ≤ t) (hz : 0 < z.re)
    (hbound : ∀ᵐ s ∂volume.restrict (Set.Ioc 0 t), ‖f s‖ ≤ M) :
    ‖∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • f s‖ ≤
      M * (1 - Real.exp (-z.re * t)) / z.re := by
  have hb : ∀ᵐ s ∂volume, s ∈ Set.Ioc 0 t →
      ‖Complex.exp (-z * ((t - s : ℝ) : ℂ)) • f s‖ ≤
        Real.exp (-z.re * (t - s)) * M := by
    filter_upwards [ae_imp_of_ae_restrict hbound] with s hs hst
    rw [norm_smul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left (hs hst) (Real.exp_pos _).le
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, Real.exp (-z.re * (t - s)) * M :=
      intervalIntegral.norm_integral_le_of_norm_le ht hb
        (Continuous.intervalIntegrable (by fun_prop) 0 t)
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_exponential_kernel hz]
      ring

end KVApproximation.Analysis
