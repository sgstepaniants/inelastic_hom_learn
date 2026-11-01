module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.Order.IsLUB

public section

open Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, half-line Green limits: agreement of tested values
among all admissible subsequential limits determines the positive-scale
limit. The tests need not separate states. -/
theorem exists_test_limit_of_unique_test_values
    {X J : Type*} (test : J → X → ℝ) (P : X → Prop) (u : ℝ → X)
    (hsub : ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] (0 : ℝ)) → (∀ n, 0 < ε n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : X, P v ∧
        ∀ j : J, Tendsto (fun n => test j (u (ε (φ n)))) atTop (𝓝 (test j v)))
    (hunique : ∀ v w : X, P v → P w → ∀ j : J, test j v = test j w) :
    ∃ v : X, P v ∧ (∀ w : X, P w → ∀ j : J, test j w = test j v) ∧
      ∀ j : J, Tendsto (fun ε => test j (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (test j v)) := by
  sorry

/-- Theorem 3.1, uniqueness of subsequential limits: a uniquely solvable
condition identifies one limit for an arbitrary family of real-valued tests.
The positive scale filter is countably generated; the test family need not be. -/
theorem exists_test_limit_of_unique_subsequences
    {X J : Type*} (test : J → X → ℝ) (P : X → Prop) (u : ℝ → X)
    (hsub : ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] (0 : ℝ)) → (∀ n, 0 < ε n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : X, P v ∧
        ∀ j : J, Tendsto (fun n => test j (u (ε (φ n)))) atTop (𝓝 (test j v)))
    (hunique : ∀ v w : X, P v → P w → v = w) :
    ∃ v : X, P v ∧ (∀ w : X, P w → w = v) ∧
      ∀ j : J, Tendsto (fun ε => test j (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (test j v)) := by
  sorry

/-- Theorem 3.1, uniqueness of subsequential limits: if every positive
approach sequence has a weakly convergent subsequence satisfying one uniquely
solvable condition, the entire positive-scale family converges weakly to
that solution. No completeness or separability assumption is needed here. -/
theorem exists_weak_limit_of_unique_subsequences
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : H → Prop) (u : ℝ → H)
    (hsub : ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] (0 : ℝ)) → (∀ n, 0 < ε n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : H, P v ∧
        ∀ ℓ : H →L[ℝ] ℝ, Tendsto (fun n => ℓ (u (ε (φ n)))) atTop (𝓝 (ℓ v)))
    (hunique : ∀ v w : H, P v → P w → v = w) :
    ∃ v : H, P v ∧ (∀ w : H, P w → w = v) ∧
      ∀ ℓ : H →L[ℝ] ℝ, Tendsto (fun ε => ℓ (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ v)) := by
  sorry

end KVApproximation.Analysis
