module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import KVApproximation.Approximation.LogPartition

/-!
# Uniform approximation and sufficient state dimension
-/

public section

open KVApproximation.Tensor KVApproximation.NeuralOperators

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

/-- Theorem 4.4 (`thm:ua`): uniform approximation over the actual material
and strain classes on the whole nonnegative time axis. The cell family is
fixed before the error tolerance and is defined by the periodic cell forms.
The tensor inputs are identified with the paper's vector inputs by Mandel
isometries. No nonemptiness assumption is imposed on the material class. -/
theorem universal_approximation :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε → ∃ nξ : ℕ,
        ∃ F ∈ Fclass nξ, ∃ G ∈ Gclass nξ,
          UniformlyApproximates C F G δ ε := by
  sorry

/-- Theorem 4.5 (`thm:sufficient_dimension`): the exact sufficient scalar
state dimension, with a separate singleton case. The logarithmic span uses
the common spectral interval; the relative error is `ε / δ`. -/
theorem sufficient_internal_variable_dimension :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε →
        let N := sufficientDimension d
          (Approximation.logarithmicSpan (αE / βV) (βE / αV)) (ε / δ)
        ∃ F ∈ Fclass N, ∃ G ∈ Gclass N,
          UniformlyApproximates C F G δ ε := by
  sorry

end KVApproximation.KelvinVoigt
