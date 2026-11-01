module

public import KVApproximation.Analysis.HalfLineLaplaceConvolution
public import KVApproximation.Analysis.CausalConvolution
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace transforms of constants and primitives

The zero-based primitive is convolution with the scalar constant one.
Exponential integrability therefore passes through time integration.
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Theorem 3.1, integrated Laplace balance: a constant initial value
has a genuinely integrable transform at every positive rate. -/
theorem integrable_halfLineLaplace_const (c : F) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t => Real.exp (-s * t) • c) (Set.Ioi (0 : ℝ)) := by
  exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).smul_const c

/-- Theorem 3.1, integrated Laplace balance: the transform of a
constant initial value is its scalar multiple by the reciprocal rate. -/
theorem halfLineLaplace_const [CompleteSpace F] (c : F) {s : ℝ} (hs : 0 < s) :
    halfLineLaplace (fun _ => c) s = s⁻¹ • c := by
  simp only [halfLineLaplace, integral_smul_const,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 0, mul_zero, Real.exp_zero,
    neg_div_neg_eq, one_div]

/-- Theorem 3.1, integrated Laplace balance: scalar convolution by
one gives the primitive on the entire nonnegative time axis. -/
private theorem posConvolution_one_eq_primitive (f : ℝ → F) {t : ℝ} (ht : 0 ≤ t) :
    posConvolution (fun _ => (1 : ℝ)) f (ContinuousLinearMap.lsmul ℝ ℝ) volume t =
      ∫ r in (0 : ℝ)..t, f r := by
  rw [posConvolution_eq_integral_sub _ _ _ ht]
  simp only [ContinuousLinearMap.lsmul_apply, one_smul]

/-- Theorem 3.1, integrated Laplace balance: the zero-based primitive
retains exponential integrability at every positive rate of the original function. -/
theorem integrable_halfLineLaplace_primitive (f : ℝ → F) {s : ℝ} (hs : 0 < s)
    (hf : IntegrableOn (fun t => Real.exp (-s * t) • f t) (Set.Ioi (0 : ℝ))) :
    IntegrableOn (fun t => Real.exp (-s * t) • (∫ r in (0 : ℝ)..t, f r))
      (Set.Ioi (0 : ℝ)) := by
  apply (integrable_halfLineLaplace_posConvolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (fun _ => (1 : ℝ)) f s
    (integrable_halfLineLaplace_const 1 hs) hf).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [posConvolution_one_eq_primitive f ht.le]

/-- Theorem 3.1, integrated Laplace balance: integration from zero
divides the Bochner Laplace transform by the positive rate. -/
theorem halfLineLaplace_primitive [CompleteSpace F] (f : ℝ → F)
    {s : ℝ} (hs : 0 < s)
    (hf : IntegrableOn (fun t => Real.exp (-s * t) • f t) (Set.Ioi (0 : ℝ))) :
    halfLineLaplace (fun t => ∫ r in (0 : ℝ)..t, f r) s =
      s⁻¹ • halfLineLaplace f s := by
  calc
    halfLineLaplace (fun t => ∫ r in (0 : ℝ)..t, f r) s =
        halfLineLaplace
          (posConvolution (fun _ => (1 : ℝ)) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) s := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [posConvolution_one_eq_primitive f ht.le]
    _ = _ := by
      rw [halfLineLaplace_posConvolution _ _ _ s
        (integrable_halfLineLaplace_const 1 hs) hf, halfLineLaplace_const 1 hs]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_one]

end KVApproximation.Analysis
