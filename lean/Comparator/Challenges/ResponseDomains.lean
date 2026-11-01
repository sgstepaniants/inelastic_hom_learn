module

public import KVApproximation.NeuralOperators.PronyResponses
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact input domains for the response maps
-/

public section

namespace KVApproximation.NeuralOperators

variable {E Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- Lemma B.12: the stress-budget and state-radius constraints form a
compact input domain. Negative budgets and radii simply allow an empty set. -/
theorem isCompact_stressInputSet {βE βV : ℝ} (hβE : 0 < βE) (hβV : 0 < βV)
    (δ radius : ℝ) : IsCompact (stressInputSet (E := E) (Q := Q) βE βV δ radius) := by
  sorry

/-- Lemma B.12: the projected velocity-state domain is compact. -/
theorem isCompact_kineticInputSet {βV : ℝ} (hβV : 0 < βV)
    (δ radius : ℝ) : IsCompact (kineticInputSet (E := E) (Q := Q) βV δ radius) := by
  sorry

end KVApproximation.NeuralOperators
