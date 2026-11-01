module

public import KVApproximation.KelvinVoigt.StripFieldProperties
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Convergence of the thin-strip coefficients
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`), coefficient convergence:
the exact finite-exponent seminorm of the strip perturbation uses its width
and the Frobenius norm of the identity tensor. -/
theorem eLpNorm_stripElasticity_sub_identity {d : ℕ} (i : Fin d) (m : ℕ)
    {p : ENNReal} (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (fun y => stripElasticity i m y - identityElasticity d) p (cellMeasure d) =
      ENNReal.ofReal ‖identityElasticity d‖ *
        (ENNReal.ofReal (1 / ((m : ℝ) + 1))) ^ (1 / p.toReal) := by
  classical
  have hfield : (fun y => stripElasticity i m y - identityElasticity d) =
      (thinStrip i m).indicator (fun _ => identityElasticity d) := by
    funext y
    by_cases hy : y ∈ thinStrip i m
    · simp only [stripElasticity, ite_eq_left hy, add_smul, one_smul,
        add_sub_cancel_right, Set.indicator_of_mem hy]
    · simp only [stripElasticity, ite_eq_right hy, add_zero, one_smul,
        sub_self, Set.indicator_of_notMem hy]
  rw [hfield]
  simpa only [cellMeasure_thinStrip, ofReal_norm] using
    (eLpNorm_indicator_const (c := identityElasticity d) (μ := cellMeasure d)
      (measurableSet_thinStrip i m).nullMeasurableSet hp hp_top)

/-- Proposition 4.7 (`prop:no_spectral_stability`), coefficient convergence:
the strip elasticities converge to the identity in every finite positive
Lp seminorm, in particular the paper's L¹ and L² topologies. -/
theorem tendsto_eLpNorm_stripElasticity_sub_identity {d : ℕ} (i : Fin d)
    {p : ENNReal} (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    Tendsto (fun m =>
      eLpNorm (fun y => stripElasticity i m y - identityElasticity d) p (cellMeasure d))
      atTop (𝓝 0) := by
  have hwidth : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [Function.comp_def, eLpNorm_stripElasticity_sub_identity i _ hp hp_top] using
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
      (c := ENNReal.ofReal ‖identityElasticity d‖) ENNReal.ofReal_ne_top
      (one_div_pos.mpr (ENNReal.toReal_pos hp hp_top))).comp hwidth

end KVApproximation.KelvinVoigt
