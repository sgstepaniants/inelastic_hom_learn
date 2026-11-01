module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Spectral.Bounds
public import KVApproximation.Spectral.TensorMeasure

/-!
# The weighted spectral measure
-/

public section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Homogenization

namespace KVApproximation.Spectral

/-- Lemma B.6 (`eq:weighted_measure_def`): the resolvent weight is
integrable against variation and defines a positive measure supported on the same interval. -/
theorem weightedMeasure_properties {d : ℕ} {lower upper c : ℝ}
    (hlower : 0 < lower) (hc : 0 < c) (ν : TensorMeasure d)
    (hνpos : ν.Positive) (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation ν Set.univ < ⊤) :
    Integrable (resolventWeight c) ν.variation ∧
      (weightedMeasure c ν).Positive ∧
      (weightedMeasure c ν).SupportedOn (Set.Icc lower upper) ∧
      totalVariation (weightedMeasure c ν) Set.univ ≤ totalVariation ν Set.univ := by
  sorry

/-- Lemma B.6, weak-continuity bridge: testing the weighted measure is
equivalent to multiplying the continuous test by the resolvent weight. -/
theorem weightedMeasure_integral {d : ℕ} {lower upper c : ℝ}
    (hlower : 0 < lower) (hc : 0 < c) (ν : TensorMeasure d)
    (hνpos : ν.Positive) (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc lower upper)) :
    Integrable f (weightedMeasure c ν).variation ∧
      tensorIntegral (weightedMeasure c ν) f =
        tensorIntegral ν (fun r => f r * resolventWeight c r) := by
  sorry

/-- Lemma B.6, quantitative estimate preceding `eq:weighted_measure_mass`:
one common bound holds before taking any supremum over materials. -/
theorem weightedMeasure_variation_le {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
    (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field)
    (ν : TensorMeasure d)
    (hν : IsSpectralRepresentation ν C.kernel (lowerRate αE βV) (upperRate βE αV)) :
    totalVariation (weightedMeasure (βE / βV) ν) Set.univ ≤
      ENNReal.ofReal (weightedVariationBound (strainDimension d) αV βV αE βE) := by
  sorry

/-- Lemma B.6 (`eq:weighted_measure_mass`): the common strict gap survives
the supremum, including an empty index type. This is the numerical step applied
to the admissible material class after the pointwise variation estimate. -/
theorem weighted_variation_sup_lt {ι : Type*} {n : ℕ} (hn : 0 < n)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE) (mass : ι → ENNReal)
    (hmass : ∀ a, mass a ≤ ENNReal.ofReal (weightedVariationBound n αV βV αE βE)) :
    (⨆ a, mass a) < ENNReal.ofReal (2 * (n : ℝ) * βV) := by
  sorry

end KVApproximation.Spectral
