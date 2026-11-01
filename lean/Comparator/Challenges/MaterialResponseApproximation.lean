module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import KVApproximation.KelvinVoigt.PronyProblem
public import KVApproximation.NeuralOperators.StateCoordinates
public import KVApproximation.Tensor.MandelFiniteIndices

/-!
# Approximation of the material-dependent Prony responses
-/

public section

open KVApproximation.Tensor KVApproximation.Approximation
open KVApproximation.Dynamics KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
variable {αV βV γV αE βE γE δ δIV η εF εG : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
variable (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE)
variable (hδ : 0 < δ) (hδIV : 0 < δIV) (hη : 0 < η)
variable (hεF : 0 < εF) (hεG : 0 < εG)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hd hVorder hγV hEorder hγE hδ hδIV hη hεF hεG

/-- Lemma B.12 (`lem:ua_step3_no`, `eq:ua_full_F_approx`,
`eq:ua_full_G_approx`): the local Prony construction admits simultaneous
response approximation on the actual material class, with scalar Mandel
state dimension and radius `δIV + η`. The positive bound `δIV` may be
chosen from Lemma B.11. -/
theorem local_prony_responses_approximate (hspan : αE / βV < βE / αV)
    {m : ℕ} (hm : 0 < m) :
    let n := logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)) * m
    let P := localPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) m
    ∀ (Fclass : StressResponseClass d (n * strainDimension d))
      (Gclass : KineticResponseClass d (n * strainDimension d)),
      HasUniversalApproximation Fclass → HasLocallyLipschitzApproximation Gclass →
      ∃ T : BlockState n (Symmetric d) ≃ₗᵢ[ℝ] InternalState (n * strainDimension d),
        (∀ q, T q = scalarBlockStrainMandel q) ∧
        ∃ F ∈ Fclass, ∃ G ∈ Gclass,
          (∀ M : admissibleMaterials d αV βV γV αE βE γE,
            ∀ x ∈ stressInputSet βE βV δ (δIV + η),
              ‖F (x, M.val) - coordinateStressResponse P T M x‖ ≤ εF) ∧
          (∀ M : admissibleMaterials d αV βV γV αE βE γE,
            ∀ x ∈ kineticInputSet βV δ (δIV + η),
              ‖G (x, M.val) - coordinateKineticResponse P T M x‖ ≤ εG) ∧
          ∀ M : admissibleMaterials d αV βV γV αE βE γE,
            LocallyLipschitz (fun x => G (x, M.val)) := by
  sorry

/-- Lemma B.12, singleton spectral interval: the exact one-term Prony
model admits the same response approximation with `strainDimension d`
scalar states, including an empty admissible material class. -/
theorem singleton_prony_responses_approximate (hspan : αE / βV = βE / αV) :
    let P := singletonPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (αE / βV)
    ∀ (Fclass : StressResponseClass d (1 * strainDimension d))
      (Gclass : KineticResponseClass d (1 * strainDimension d)),
      HasUniversalApproximation Fclass → HasLocallyLipschitzApproximation Gclass →
      ∃ T : BlockState 1 (Symmetric d) ≃ₗᵢ[ℝ] InternalState (1 * strainDimension d),
        (∀ q, T q = scalarBlockStrainMandel q) ∧
        ∃ F ∈ Fclass, ∃ G ∈ Gclass,
          (∀ M : admissibleMaterials d αV βV γV αE βE γE,
            ∀ x ∈ stressInputSet βE βV δ (δIV + η),
              ‖F (x, M.val) - coordinateStressResponse P T M x‖ ≤ εF) ∧
          (∀ M : admissibleMaterials d αV βV γV αE βE γE,
            ∀ x ∈ kineticInputSet βV δ (δIV + η),
              ‖G (x, M.val) - coordinateKineticResponse P T M x‖ ≤ εG) ∧
          ∀ M : admissibleMaterials d αV βV γV αE βE γE,
            LocallyLipschitz (fun x => G (x, M.val)) := by
  sorry

end KVApproximation.KelvinVoigt
