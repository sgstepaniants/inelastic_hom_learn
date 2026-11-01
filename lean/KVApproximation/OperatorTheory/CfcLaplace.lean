module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import KVApproximation.Analysis.HalfLineLaplaceProperties
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral

/-!
# Laplace transforms of positive self-adjoint functional calculus
-/

public section

open MeasureTheory KVApproximation.Analysis

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, transform of the relaxation kernel: one scalar
integrable majorant controls the whole nonnegative spectrum. The norm
of the identity is retained so the zero Hilbert space is included. -/
private theorem cfc_memory_majorant (R : H →L[ℝ] H)
    (hpos : ∀ r ∈ spectrum ℝ R, 0 ≤ r) (s : ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ r ∈ spectrum ℝ R,
      ‖Real.exp (-s * t) * (r * Real.exp (-r * t))‖ ≤
        Real.exp (-s * t) * (‖R‖ * ‖(1 : H →L[ℝ] H)‖) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  intro r hr
  have hr0 := hpos r hr
  have hrB : r ≤ ‖R‖ * ‖(1 : H →L[ℝ] H)‖ :=
    (le_abs_self r).trans (spectrum.norm_le_norm_mul_of_mem hr)
  have he : Real.exp (-r * t) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr0) ht.le)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.exp_pos _).le (mul_nonneg hr0 (Real.exp_pos _).le))]
  exact mul_le_mul_of_nonneg_left
    ((mul_le_of_le_one_right hr0 he).trans hrB) (Real.exp_pos _).le

/-- Theorem 3.1, transform of the relaxation kernel: the positive
self-adjoint spectral function r exp(-tr) is Bochner integrable in operator
norm after multiplication by any positive-rate exponential. -/
theorem integrable_cfc_memory_laplace (R : H →L[ℝ] H)
    (hR : IsSelfAdjoint R) (hpos : ∀ r ∈ spectrum ℝ R, 0 ≤ r)
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) •
      cfc (fun r : ℝ => r * Real.exp (-r * t)) R) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_cfc measurableSet_Ioi
    (fun t r : ℝ => Real.exp (-s * t) * (r * Real.exp (-r * t)))
    (fun t : ℝ => Real.exp (-s * t) * (‖R‖ * ‖(1 : H →L[ℝ] H)‖)) R
    (by fun_prop) (cfc_memory_majorant R hpos s)
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const
      (‖R‖ * ‖(1 : H →L[ℝ] H)‖)).hasFiniteIntegral hR
  apply h.congr
  exact Filter.Eventually.of_forall fun t =>
    cfc_const_mul (Real.exp (-s * t)) (fun r : ℝ => r * Real.exp (-r * t)) R (by fun_prop)

/-- Theorem 3.1, transform of the relaxation kernel: integrating the
continuous functional calculus gives the exact resolvent multiplier r/(s+r).
The underlying Hilbert space need not be finite-dimensional or separable. -/
theorem halfLineLaplace_cfc_memory (R : H →L[ℝ] H)
    (hR : IsSelfAdjoint R) (hpos : ∀ r ∈ spectrum ℝ R, 0 ≤ r)
    {s : ℝ} (hs : 0 < s) :
    halfLineLaplace (fun t : ℝ => cfc (fun r : ℝ => r * Real.exp (-r * t)) R) s =
      cfc (fun r : ℝ => r / (s + r)) R := by
  have hcomm := cfc_setIntegral measurableSet_Ioi
    (fun t r : ℝ => Real.exp (-s * t) * (r * Real.exp (-r * t)))
    (fun t : ℝ => Real.exp (-s * t) * (‖R‖ * ‖(1 : H →L[ℝ] H)‖)) R
    (by fun_prop) (cfc_memory_majorant R hpos s)
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const
      (‖R‖ * ‖(1 : H →L[ℝ] H)‖)).hasFiniteIntegral hR
  have hscalar (r : ℝ) (hr : r ∈ spectrum ℝ R) :
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * t) * (r * Real.exp (-r * t))) =
        r / (s + r) := by
    have hf (t : ℝ) : Real.exp (-s * t) * (r * Real.exp (-r * t)) =
        r * Real.exp (-(s + r) * t) := by
      rw [show -(s + r) * t = -s * t + -r * t by ring, Real.exp_add]
      ring
    simp_rw [hf]
    rw [integral_const_mul,
      integral_exp_mul_Ioi (neg_lt_zero.mpr (add_pos_of_pos_of_nonneg hs (hpos r hr))) 0]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ),
        cfc (fun r : ℝ => Real.exp (-s * t) * (r * Real.exp (-r * t))) R := by
      unfold halfLineLaplace
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t =>
        (cfc_const_mul (Real.exp (-s * t)) (fun r : ℝ => r * Real.exp (-r * t)) R
          (by fun_prop)).symm
    _ = cfc (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-s * t) * (r * Real.exp (-r * t))) R := hcomm.symm
    _ = _ := cfc_congr hscalar

end KVApproximation.OperatorTheory
