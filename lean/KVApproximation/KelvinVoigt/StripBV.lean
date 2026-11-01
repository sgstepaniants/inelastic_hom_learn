module

public import KVApproximation.KelvinVoigt.StripFieldProperties
public import KVApproximation.Analysis.PeriodicStripVariation

/-!
# Uniform bounds for the thin-strip coefficients
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`), coefficient bounds:
the normalized-cell Lp seminorm of the strip elasticity is at most twice
the Frobenius norm of the identity, for every exponent. -/
theorem eLpNorm_stripElasticity_le {d : ℕ} (i : Fin d) (m : ℕ) (p : ENNReal) :
    eLpNorm (stripElasticity i m) p (cellMeasure d) ≤
      ENNReal.ofReal (2 * ‖identityElasticity d‖) := by
  classical
  have hbound (y : PeriodicCell d) : ‖stripElasticity i m y‖ ≤ 2 * ‖identityElasticity d‖ := by
    by_cases hy : y ∈ thinStrip i m
    · simp only [stripElasticity, ite_eq_left hy, norm_smul, Real.norm_eq_abs]
      norm_num
    · simp only [stripElasticity, ite_eq_right hy, add_zero, one_smul]
      linarith [norm_nonneg (identityElasticity d)]
  simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
    (eLpNorm_le_of_ae_bound (p := p) (μ := cellMeasure d)
      (measurable_stripElasticity i m).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound))

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip variation:
the two periodic faces give a uniform bound independent of the width. -/
theorem periodicVariation_stripElasticity_le {d : ℕ} (i : Fin d) (m : ℕ) :
    periodicVariation (stripElasticity i m) ≤ ENNReal.ofReal (2 * ‖identityElasticity d‖) := by
  classical
  have hfield : stripElasticity i m = fun y => identityElasticity d +
      (thinStrip i m).indicator (fun _ => identityElasticity d) y := by
    funext y
    by_cases hy : y ∈ thinStrip i m
    · simp only [stripElasticity, ite_eq_left hy, add_smul, one_smul,
        Set.indicator_of_mem hy]
    · simp only [stripElasticity, ite_eq_right hy, add_zero, one_smul,
        Set.indicator_of_notMem hy]
  have hpos : 0 < (m : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
  have hwidth : 1 / ((m : ℝ) + 1) ≤ 1 :=
    (div_le_one hpos).2 (le_add_of_nonneg_left (Nat.cast_nonneg m))
  rw [hfield]
  exact periodicVariation_const_add_coordinate_strip_le i (identityElasticity d)
    (identityElasticity d) (one_div_nonneg.mpr hpos.le) hwidth

/-- Proposition 4.7 (`prop:no_spectral_stability`), limiting material:
the full BV norm of the constant identity field equals its Frobenius norm. -/
theorem periodicBVNorm_identityElasticity (d : ℕ) :
    periodicBVNorm (fun _ : PeriodicCell d => identityElasticity d) =
      ENNReal.ofReal ‖identityElasticity d‖ := by
  rw [periodicBVNorm, periodicVariation_const, add_zero]
  simpa only [measure_univ, ENNReal.one_rpow, mul_one, ofReal_norm] using
    (eLpNorm_const' (μ := cellMeasure d) (identityElasticity d)
      (by norm_num : (1 : ENNReal) ≠ 0) (by norm_num : (1 : ENNReal) ≠ ⊤))

/-- Proposition 4.7 (`prop:no_spectral_stability`), common admissible class:
the L¹ and variation terms give one uniform full BV bound. -/
theorem periodicBVNorm_stripElasticity_le {d : ℕ} (i : Fin d) (m : ℕ) :
    periodicBVNorm (stripElasticity i m) ≤ ENNReal.ofReal (4 * ‖identityElasticity d‖) := by
  have hnorm : 0 ≤ 2 * ‖identityElasticity d‖ := mul_nonneg (by norm_num) (norm_nonneg _)
  calc
    _ ≤ ENNReal.ofReal (2 * ‖identityElasticity d‖) +
        ENNReal.ofReal (2 * ‖identityElasticity d‖) :=
      add_le_add (eLpNorm_stripElasticity_le i m 1) (periodicVariation_stripElasticity_le i m)
    _ = ENNReal.ofReal (4 * ‖identityElasticity d‖) := by
      rw [← ENNReal.ofReal_add hnorm hnorm]
      congr 1
      ring

end KVApproximation.KelvinVoigt
