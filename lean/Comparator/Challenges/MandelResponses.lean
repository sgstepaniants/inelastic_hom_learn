module

public import KVApproximation.KelvinVoigt.MandelResponses

/-!
# Mandel response classes and the scalar approximation hypotheses
-/

public section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Analysis KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

/-- Example 2.1 and Lemma B.12: the selected strain equivalence is the
prescribed Mandel map. -/
theorem strainMandelEquiv_apply {d : ℕ} (e : Symmetric d) :
    strainMandelEquiv d e = scalarStrainMandel e := by
  sorry

/-- Example 2.1 and Lemma B.12: the selected elasticity equivalence
is the prescribed fourth-order Mandel map. -/
theorem elasticityMandelEquiv_apply {d : ℕ} (A : Elasticity d) :
    elasticityMandelEquiv d A = scalarElasticityMandel A := by
  sorry

/-- Lemma B.12 (`eq:F_and_G`): the material coordinate homeomorphism
agrees almost everywhere with the concatenated Mandel vectors of the two
actual coefficient fields. -/
theorem materialMandelCoordinates_ae {d : ℕ} (M : Material d) :
    ∀ᵐ y ∂cellMeasure d, materialMandelCoordinates d M y =
      materialValueCoordinates d (WithLp.toLp 2
        (scalarElasticityMandel (M.1 y), scalarElasticityMandel (M.2 y))) := by
  sorry

/-- Lemma B.12: A1 for the scalar neural mappings implies A1 for the
induced tensor stress responses with the same approximation tolerance. -/
theorem mandelStressClass_hasUniversalApproximation {d nξ : ℕ}
    (N : Set C(EuclideanSpace ℝ (Fin (2 * strainDimension d + nξ)) × ScalarMaterial d,
      EuclideanSpace ℝ (Fin (strainDimension d))))
    (hN : HasUniversalApproximation N) :
    HasUniversalApproximation (mandelStressClass d nξ N) := by
  sorry

/-- Lemma B.12: A2 for scalar neural mappings implies A2 for the
induced kinetic responses, preserving the full-input local Lipschitz property. -/
theorem mandelKineticClass_hasLocallyLipschitzApproximation {d nξ : ℕ}
    (N : Set C(EuclideanSpace ℝ (Fin (strainDimension d + nξ)) × ScalarMaterial d,
      EuclideanSpace ℝ (Fin nξ)))
    (hN : HasLocallyLipschitzApproximation N) :
    HasLocallyLipschitzApproximation (mandelKineticClass d nξ N) := by
  sorry

end KVApproximation.KelvinVoigt
