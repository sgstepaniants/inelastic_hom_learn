module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Weak subsequences in Hilbert space
-/

public section

open Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, static homogenization: a bounded sequence in a complete
real Hilbert space has a weakly convergent subsequence with the same norm bound.
No separability assumption on the ambient space is needed. -/
theorem exists_weakly_convergent_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ uLim : H, ‖uLim‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ℓ : H →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  sorry

end KVApproximation.Analysis
