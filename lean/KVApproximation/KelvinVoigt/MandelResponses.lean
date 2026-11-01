module

public import KVApproximation.KelvinVoigt.Material
public import KVApproximation.NeuralOperators.ResponseModel
public import KVApproximation.NeuralOperators.CoordinateClasses
public import KVApproximation.Tensor.MandelFiniteIsometry
public import KVApproximation.Analysis.LpCoordinates
public import KVApproximation.Analysis.LpProductCoordinates
public import KVApproximation.Analysis.EuclideanCoordinates

/-!
# Scalar Mandel coordinates for the response classes
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Analysis KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

/-- Example 2.1 (`eq:F_and_G`): the prescribed scalar strain isometry. -/
def strainMandelEquiv (d : ℕ) :
    Symmetric d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (strainDimension d)) :=
  (scalarStrainMandel_isometry d).choose

/-- Example 2.1 (`eq:F_and_G`): the prescribed scalar elasticity isometry. -/
def elasticityMandelEquiv (d : ℕ) :
    Elasticity d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (elasticityDimension d)) :=
  (scalarElasticityMandel_isometry d).choose

/-- Section 4.1: one material channel field contains the viscosity and
elasticity Mandel vectors, with exactly `2 * elasticityDimension d` channels. -/
abbrev ScalarMaterial (d : ℕ) :=
  Lp (EuclideanSpace ℝ (Fin (2 * elasticityDimension d))) 2 (cellMeasure d)

/-- Lemma B.12: concatenate two scalar elasticity vectors in the order
viscosity, elasticity. -/
def materialValueCoordinates (d : ℕ) :
    WithLp 2 (EuclideanSpace ℝ (Fin (elasticityDimension d)) ×
      EuclideanSpace ℝ (Fin (elasticityDimension d))) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (2 * elasticityDimension d)) :=
  (appendEuclidean (elasticityDimension d) (elasticityDimension d)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (by omega)))

/-- Lemma B.12: apply fourth-order Mandel coordinates to each material
field and combine them into the single L² channel field used by A1/A2. -/
def materialMandelCoordinates (d : ℕ) : Material d ≃ₜ ScalarMaterial d :=
  let V := (lp_coordinates (cellMeasure d) 2 (elasticityMandelEquiv d)).choose
  let P := (lp_product_coordinates (E := EuclideanSpace ℝ (Fin (elasticityDimension d)))
    (F := EuclideanSpace ℝ (Fin (elasticityDimension d))) (cellMeasure d)).choose
  let A := (lp_coordinates (cellMeasure d) 2 (materialValueCoordinates d)).choose
  ((V.toHomeomorph.prodCongr V.toHomeomorph).trans P.toHomeomorph).trans A.toHomeomorph

/-- Lemma B.12: concatenate strain-velocity and internal-state inputs,
preserving the Euclidean norm and exact scalar input dimension. -/
def kineticMandelCoordinates (d nξ : ℕ) :
    KineticInput (Symmetric d) (EuclideanSpace ℝ (Fin nξ)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (strainDimension d + nξ)) :=
  (LinearIsometryEquiv.withLpProdCongr 2 (strainMandelEquiv d)
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin nξ)))).trans
      (appendEuclidean (strainDimension d) nξ)

/-- Lemma B.12: concatenate strain, strain velocity and internal state,
with exactly `2 * strainDimension d + nξ` scalar inputs. -/
def stressMandelCoordinates (d nξ : ℕ) :
    StressInput (Symmetric d) (EuclideanSpace ℝ (Fin nξ)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (2 * strainDimension d + nξ)) :=
  ((LinearIsometryEquiv.withLpProdCongr 2 (strainMandelEquiv d)
    (kineticMandelCoordinates d nξ)).trans
      (appendEuclidean (strainDimension d) (strainDimension d + nξ))).trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (by omega)))

/-- Section 4.1 (`eq:stress_response`): the tensor stress response class
induced by a class of scalar neural mappings. -/
def mandelStressClass (d nξ : ℕ)
    (N : Set C(EuclideanSpace ℝ (Fin (2 * strainDimension d + nξ)) × ScalarMaterial d,
      EuclideanSpace ℝ (Fin (strainDimension d)))) :=
  inducedResponseClass (stressMandelCoordinates d nξ).toIsometryEquiv
    (materialMandelCoordinates d) (strainMandelEquiv d) N

/-- Section 4.1 (`eq:kinetic_response`): the kinetic response class
induced by scalar mappings; the scalar state output needs no decoding. -/
def mandelKineticClass (d nξ : ℕ)
    (N : Set C(EuclideanSpace ℝ (Fin (strainDimension d + nξ)) × ScalarMaterial d,
      EuclideanSpace ℝ (Fin nξ))) :=
  inducedResponseClass (kineticMandelCoordinates d nξ).toIsometryEquiv
    (materialMandelCoordinates d) (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin nξ))) N

end KVApproximation.KelvinVoigt
