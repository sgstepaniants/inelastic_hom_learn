module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import KVApproximation.Approximation.AlternativeDimension
public import KVApproximation.Approximation.LogPartition

/-!
# Neural approximation with alternative Prony dimensions
-/

public section

open KVApproximation.Tensor KVApproximation.NeuralOperators KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} (hd : d = 1 ∨ d = 2 ∨ d = 3)
variable {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
variable (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE) (hδ : 0 < δ)
variable (Fclass : ∀ nξ : ℕ, StressResponseClass d nξ)
variable (Gclass : ∀ nξ : ℕ, KineticResponseClass d nξ)
variable (hF : ∀ nξ, HasUniversalApproximation (Fclass nξ))
variable (hG : ∀ nξ, HasLocallyLipschitzApproximation (Gclass nξ))

include hd hVorder hγV hEorder hγE hδ hF hG

/-- Remark 4.6, unweighted construction: the first alternative establishes
Theorem 4.4 at its stated sufficient dimension. The singleton case uses
one symmetric-tensor state; the cell family is fixed before the tolerance. -/
theorem unweighted_sufficient_internal_variable_dimension :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε →
        let R := logarithmicSpan (αE / βV) (βE / αV)
        let N := if R = 0 then strainDimension d else
          unweightedDimension (strainDimension d) R (ε / δ) (βE / αE)
        ∃ F ∈ Fclass N, ∃ G ∈ Gclass N,
          UniformlyApproximates C F G δ ε := by
  sorry

/-- Remark 4.6, global weighted construction: the second alternative
establishes Theorem 4.4 at its stated sufficient dimension, with every
positive logarithmic span and the separate exact singleton case. -/
theorem global_sufficient_internal_variable_dimension :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε →
        let R := logarithmicSpan (αE / βV) (βE / αV)
        let N := if R = 0 then strainDimension d else
          globalPronyDimension (strainDimension d) R (ε / δ)
        ∃ F ∈ Fclass N, ∃ G ∈ Gclass N,
          UniformlyApproximates C F G δ ε := by
  sorry

end KVApproximation.KelvinVoigt
