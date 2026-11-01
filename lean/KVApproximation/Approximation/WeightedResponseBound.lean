module

public import KVApproximation.Approximation.WeightedResponse
public import KVApproximation.Analysis.ExponentialIntegralBounds
public import KVApproximation.Dynamics.ExponentialConvolution
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# The right-half-plane estimate for the weighted response

Integration by parts bounds the velocity convolution by the strain amplitude;
direct integration bounds it by the velocity amplitude. Their combination
gives the paper's stress-scaled bound uniformly in time.
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Analysis

namespace KVApproximation.Approximation

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- Lemma B.7 (`eq:weighted_response_bound`): the uniform bound in the
open right half-plane, with the original stress-scale constraint. -/
theorem norm_weightedResponse_le (J : E →ₗᵢ[ℝ] F)
    (e : BoundedTrajectory E) {βE βV δ t : ℝ} {z : ℂ}
    (hβE : 0 < βE) (hβV : 0 < βV)
    (he : e.Admissible βE βV δ) (ht : 0 ≤ t) (hz : 0 < z.re) :
    ‖weightedResponse J.toContinuousLinearMap (βE / βV) e t z‖ ≤
      (1 + ‖z‖ / z.re) * δ / βV := by
  let q := ∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • J (e.velocity s)
  let p := ∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • J (e.value s)
  let a := Real.exp (-z.re * t)
  let c := ‖z‖ / z.re
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have hc1 : 1 ≤ c := (le_div_iff₀ hz).mpr (by simpa using Complex.re_le_norm z)
  have hvalue : 0 ≤ e.valueBound := ENNReal.toReal_nonneg
  have hvelocity : 0 ≤ e.velocityBound := ENNReal.toReal_nonneg
  have hvbound : ∀ᵐ s ∂volume.restrict (Set.Ioc 0 t), ‖J (e.velocity s)‖ ≤ e.velocityBound := by
    have hh := ae_restrict_of_ae_restrict_of_subset
      (show Set.Ioc 0 t ⊆ Set.Ici 0 from fun _ hs => hs.1.le) e.norm_velocity_ae_le
    simpa only [J.norm_map] using hh
  have hubound : ∀ᵐ s ∂volume.restrict (Set.Ioc 0 t), ‖J (e.value s)‖ ≤ e.valueBound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [J.norm_map]
    exact e.norm_value_le hs.1.le
  have hq := norm_exponential_integral_le (fun s => J (e.velocity s)) ht hz hvbound
  have hp := norm_exponential_integral_le (fun s => J (e.value s)) ht hz hubound
  change ‖q‖ ≤ e.velocityBound * (1 - a) / z.re at hq
  change ‖p‖ ≤ e.valueBound * (1 - a) / z.re at hp
  have hqvel : ‖z‖ * ‖q‖ ≤ c * e.velocityBound := by
    calc
      ‖z‖ * ‖q‖ ≤ ‖z‖ * (e.velocityBound * (1 - a) / z.re) :=
        mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      _ ≤ ‖z‖ * (e.velocityBound / z.re) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply div_le_div_of_nonneg_right _ hz.le
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (sub_le_self 1 ha0) hvelocity
      _ = c * e.velocityBound := by dsimp [c]; ring
  have hqvalue : ‖q‖ ≤ (1 + c) * e.valueBound := by
    have heq := e.exponential_integral_eq J.toContinuousLinearMap ht z
    change q = J (e.value t) - Complex.exp (-z * (t : ℂ)) • J (e.value 0) - z • p at heq
    have hnexp : ‖Complex.exp (-z * (t : ℂ))‖ = a := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, a]
    calc
      ‖q‖ ≤ (‖J (e.value t)‖ + ‖Complex.exp (-z * (t : ℂ)) • J (e.value 0)‖) +
          ‖z • p‖ := by
        rw [heq]
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ = ‖e.value t‖ + a * ‖e.value 0‖ + ‖z‖ * ‖p‖ := by
        rw [norm_smul, norm_smul, hnexp, J.norm_map, J.norm_map]
      _ ≤ e.valueBound + a * e.valueBound +
          ‖z‖ * (e.valueBound * (1 - a) / z.re) :=
        add_le_add (add_le_add (e.norm_value_le ht)
          (mul_le_mul_of_nonneg_left (e.norm_value_le le_rfl) ha0))
          (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
      _ = (1 + a + c * (1 - a)) * e.valueBound := by dsimp [c]; ring
      _ ≤ (1 + c) * e.valueBound := by
        apply mul_le_mul_of_nonneg_right _ hvalue
        nlinarith
  have hscale : 0 ≤ βE / βV := (div_pos hβE hβV).le
  have hscalar : ‖((βE / βV : ℝ) : ℂ) + z‖ ≤ βE / βV + ‖z‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscale] using
      norm_add_le ((βE / βV : ℝ) : ℂ) z
  change ‖(((βE / βV : ℝ) : ℂ) + z) • q‖ ≤ _
  calc
    _ = ‖((βE / βV : ℝ) : ℂ) + z‖ * ‖q‖ := norm_smul _ _
    _ ≤ (βE / βV + ‖z‖) * ‖q‖ := mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
    _ = βE / βV * ‖q‖ + ‖z‖ * ‖q‖ := add_mul _ _ _
    _ ≤ βE / βV * ((1 + c) * e.valueBound) + c * e.velocityBound :=
      add_le_add (mul_le_mul_of_nonneg_left hqvalue hscale) hqvel
    _ ≤ βE / βV * ((1 + c) * e.valueBound) + (1 + c) * e.velocityBound := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (show c ≤ 1 + c by linarith) hvelocity)
    _ = ((1 + c) / βV) * (βE * e.valueBound + βV * e.velocityBound) := by
      field_simp
    _ ≤ ((1 + c) / βV) * δ :=
      mul_le_mul_of_nonneg_left he (div_nonneg (by linarith) hβV.le)
    _ = (1 + ‖z‖ / z.re) * δ / βV := by dsimp [c]; ring

end KVApproximation.Approximation
