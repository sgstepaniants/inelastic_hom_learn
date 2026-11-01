module

public import KVApproximation.Spectral.Bounds
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.Ring

/-!
# The strict weighted-mass gap
-/

public section

namespace KVApproximation.Spectral

/-- Lemma B.6, proof: the explicit common bound is strictly below
`2 * tensorDimension * viscosityUpper`. -/
theorem weightedVariationBound_lt {tensorDimension : ℕ} (hdim : 0 < tensorDimension)
    {viscosityLower viscosityUpper elasticityLower elasticityUpper : ℝ}
    (hvl : 0 < viscosityLower) (hvu : 0 < viscosityUpper)
    (hel : 0 < elasticityLower) (heu : 0 < elasticityUpper) :
    weightedVariationBound tensorDimension viscosityLower viscosityUpper
      elasticityLower elasticityUpper < 2 * (tensorDimension : ℝ) * viscosityUpper := by
  have hratio : 0 < viscosityUpper * elasticityLower / elasticityUpper :=
    div_pos (mul_pos hvu hel) heu
  have hgap : 2 * viscosityUpper - viscosityLower -
      viscosityUpper * elasticityLower / elasticityUpper < 2 * viscosityUpper :=
    (sub_lt_self _ hratio).trans (sub_lt_self _ hvl)
  calc
    weightedVariationBound tensorDimension viscosityLower viscosityUpper
        elasticityLower elasticityUpper < (tensorDimension : ℝ) * (2 * viscosityUpper) :=
      mul_lt_mul_of_pos_left hgap (Nat.cast_pos.mpr hdim)
    _ = 2 * (tensorDimension : ℝ) * viscosityUpper := by ring

/-- Lemma B.6 (`eq:weighted_measure_mass`): the common strict gap survives
the supremum, including an empty index type. -/
theorem weighted_variation_sup_lt {ι : Type*} {n : ℕ} (hn : 0 < n)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE) (mass : ι → ENNReal)
    (hmass : ∀ a, mass a ≤ ENNReal.ofReal (weightedVariationBound n αV βV αE βE)) :
    (⨆ a, mass a) < ENNReal.ofReal (2 * (n : ℝ) * βV) := by
  apply (iSup_le hmass).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (mul_pos (by norm_num)
    (Nat.cast_pos.mpr hn)) hβV)).2
  exact weightedVariationBound_lt hn hαV hβV hαE hβE

end KVApproximation.Spectral
