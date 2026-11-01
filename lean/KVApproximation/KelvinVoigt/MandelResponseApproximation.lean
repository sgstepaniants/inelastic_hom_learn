module

public import KVApproximation.KelvinVoigt.MandelResponses
public import KVApproximation.NeuralOperators.CoordinateApproximation

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
  exact (scalarStrainMandel_isometry d).choose_spec e

/-- Example 2.1 and Lemma B.12: the selected elasticity equivalence
is the prescribed fourth-order Mandel map. -/
theorem elasticityMandelEquiv_apply {d : ℕ} (A : Elasticity d) :
    elasticityMandelEquiv d A = scalarElasticityMandel A := by
  exact (scalarElasticityMandel_isometry d).choose_spec A

/-- Lemma B.12 (`eq:F_and_G`): the material coordinate homeomorphism
agrees almost everywhere with the concatenated Mandel vectors of the two
actual coefficient fields. -/
theorem materialMandelCoordinates_ae {d : ℕ} (M : Material d) :
    ∀ᵐ y ∂cellMeasure d, materialMandelCoordinates d M y =
      materialValueCoordinates d (WithLp.toLp 2
        (scalarElasticityMandel (M.1 y), scalarElasticityMandel (M.2 y))) := by
  let V := (lp_coordinates (cellMeasure d) 2 (elasticityMandelEquiv d)).choose
  let P := (lp_product_coordinates (E := EuclideanSpace ℝ (Fin (elasticityDimension d)))
    (F := EuclideanSpace ℝ (Fin (elasticityDimension d))) (cellMeasure d)).choose
  let A := (lp_coordinates (cellMeasure d) 2 (materialValueCoordinates d)).choose
  change ∀ᵐ y ∂cellMeasure d, A (P (V M.1, V M.2)) y = _
  filter_upwards [(lp_coordinates (cellMeasure d) 2 (materialValueCoordinates d)).choose_spec
      (P (V M.1, V M.2)),
    (lp_product_coordinates (E := EuclideanSpace ℝ (Fin (elasticityDimension d)))
      (F := EuclideanSpace ℝ (Fin (elasticityDimension d))) (cellMeasure d)).choose_spec
      (V M.1, V M.2),
    (lp_coordinates (cellMeasure d) 2 (elasticityMandelEquiv d)).choose_spec M.1,
    (lp_coordinates (cellMeasure d) 2 (elasticityMandelEquiv d)).choose_spec M.2]
      with y hA hP hV₁ hV₂
  change A (P (V M.1, V M.2)) y = _ at hA
  change P (V M.1, V M.2) y = _ at hP
  change V M.1 y = _ at hV₁
  change V M.2 y = _ at hV₂
  rw [hA, hP, hV₁, hV₂, elasticityMandelEquiv_apply, elasticityMandelEquiv_apply]

/-- Lemma B.12: A1 for the scalar neural mappings implies A1 for the
induced tensor stress responses with the same approximation tolerance. -/
theorem mandelStressClass_hasUniversalApproximation {d nξ : ℕ}
    (N : Set C(EuclideanSpace ℝ (Fin (2 * strainDimension d + nξ)) × ScalarMaterial d,
      EuclideanSpace ℝ (Fin (strainDimension d))))
    (hN : HasUniversalApproximation N) :
    HasUniversalApproximation (mandelStressClass d nξ N) := by
  exact hN.inducedResponseClass (stressMandelCoordinates d nξ).toIsometryEquiv
    (materialMandelCoordinates d) (strainMandelEquiv d)

/-- Lemma B.12: A2 for scalar neural mappings implies A2 for the
induced kinetic responses, preserving the full-input local Lipschitz property. -/
theorem mandelKineticClass_hasLocallyLipschitzApproximation {d nξ : ℕ}
    (N : Set C(EuclideanSpace ℝ (Fin (strainDimension d + nξ)) × ScalarMaterial d,
      EuclideanSpace ℝ (Fin nξ)))
    (hN : HasLocallyLipschitzApproximation N) :
    HasLocallyLipschitzApproximation (mandelKineticClass d nξ N) := by
  exact hN.inducedResponseClass (kineticMandelCoordinates d nξ).toIsometryEquiv
    (materialMandelCoordinates d) (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin nξ)))

end KVApproximation.KelvinVoigt
