module

public import KVApproximation.NeuralOperators.CoordinateClasses

/-!
# Approximation properties under coordinate transport
-/

public section

namespace KVApproximation.NeuralOperators

variable {X X' M M' F F' : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace X']
  [TopologicalSpace M] [TopologicalSpace M']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- Lemma B.12: compact-image transport and output isometry preserve A1
with the same approximation tolerance. -/
theorem HasUniversalApproximation.inducedResponseClass
    (S : X ≃ᵢ X') (U : M ≃ₜ M') (T : F ≃ₗᵢ[ℝ] F')
    {N : Set C(X' × M', F')} (hN : HasUniversalApproximation N) :
    HasUniversalApproximation (inducedResponseClass S U T N) := by
  sorry

/-- Lemma B.12: the same compact-image construction preserves A2,
including local Lipschitz regularity in the full vector input. -/
theorem HasLocallyLipschitzApproximation.inducedResponseClass
    (S : X ≃ᵢ X') (U : M ≃ₜ M') (T : F ≃ₗᵢ[ℝ] F')
    {N : Set C(X' × M', F')} (hN : HasLocallyLipschitzApproximation N) :
    HasLocallyLipschitzApproximation (inducedResponseClass S U T N) := by
  sorry

end KVApproximation.NeuralOperators
