module

public import Mathlib.Analysis.InnerProductSpace.Dual

public section

open Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, half-line compactness: one strictly increasing subsequence
converges weakly in every member of a countable family of complete Hilbert spaces,
retaining the individual norm bounds and requiring no ambient separability. -/
theorem exists_weakly_convergent_diagonal_subsequence
    {H : ℕ → Type*} [∀ k, NormedAddCommGroup (H k)]
    [∀ k, InnerProductSpace ℝ (H k)] [∀ k, CompleteSpace (H k)]
    (u : ∀ k, ℕ → H k) (C : ℕ → ℝ) (hu : ∀ k n, ‖u k n‖ ≤ C k) :
    ∃ uLim : ∀ k, H k, (∀ k, ‖uLim k‖ ≤ C k) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k (ℓ : H k →L[ℝ] ℝ),
        Tendsto (fun n => ℓ (u k (φ n))) atTop (𝓝 (ℓ (uLim k))) := by
  sorry

end KVApproximation.Analysis
