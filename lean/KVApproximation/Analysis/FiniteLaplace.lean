module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic.Linarith

/-!
# Entire finite-time exponential convolutions

Differentiation in the complex rate is justified by an integrable bound
uniform on a neighborhood of each rate.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Lemma B.7, analyticity argument: a finite-time exponential convolution
of a Bochner-integrable function is entire in its complex rate. -/
theorem finiteLaplace_entire {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (f : ℝ → F) {t : ℝ} (ht : 0 ≤ t) (hf : IntervalIntegrable f volume 0 t) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • f s)
      Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro z₀
  have hmeas := hf.def'.aestronglyMeasurable
  have hexp (z : ℂ) : Continuous (fun s : ℝ => Complex.exp (-z * ((t - s : ℝ) : ℂ))) := by
    fun_prop
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun z s => (Complex.exp (-z * ((t - s : ℝ) : ℂ)) * (-((t - s : ℝ) : ℂ))) • f s)
    (bound := fun s => (Real.exp ((‖z₀‖ + 1) * t) * t) * ‖f s‖)
    (Metric.ball_mem_nhds z₀ zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2.differentiableAt
  · exact Filter.Eventually.of_forall fun z => (hexp z).aestronglyMeasurable.smul hmeas
  · exact hf.continuousOn_smul (hexp z₀).continuousOn
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).smul hmeas
  · filter_upwards with s hs z hz
    rw [Set.uIoc_of_le ht] at hs
    have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
    have hts' : t - s ≤ t := sub_le_self _ hs.1.le
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have hd := Metric.mem_ball.mp hz
      have hn := norm_add_le (z - z₀) z₀
      rw [sub_add_cancel] at hn
      rw [dist_eq_norm] at hd
      linarith
    have harg : ‖-z * ((t - s : ℝ) : ℂ)‖ ≤ (‖z₀‖ + 1) * t := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hts]
      exact mul_le_mul hz' hts' hts (by positivity)
    have he : ‖Complex.exp (-z * ((t - s : ℝ) : ℂ))‖ ≤
        Real.exp ((‖z₀‖ + 1) * t) :=
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr harg)
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hts]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul he hts' hts (Real.exp_pos _).le) (norm_nonneg _)
  · exact hf.norm.const_mul _
  · filter_upwards with s _ z _
    simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul] using
      (((hasDerivAt_id z).neg.mul_const (((t - s : ℝ) : ℂ))).cexp.smul_const (f s))

end KVApproximation.Analysis
