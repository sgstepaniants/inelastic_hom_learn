module

public import KVApproximation.Analysis.TimeSobolev

public section

open Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), forced Sobolev limit:
a bounded H¹ sequence with prescribed pointwise weak trace limits has a weak
subsequence whose continuous trace is that prescribed limit, including both endpoints. -/
theorem TimeH1.exists_weak_subsequence_with_trace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : ℝ} (hT : 0 < T) (u : ℕ → TimeH1 H T) {C : ℝ}
    (hbound : ∀ n, ‖u n‖ ≤ C) (v : Set.Icc (0 : ℝ) T → H)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (TimeH1.trace hT (u n) t)) atTop (𝓝 (ℓ (v t)))) :
    ∃ uLim : TimeH1 H T, ‖uLim‖ ≤ C ∧
      (∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace hT uLim t = v t) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  sorry

end KVApproximation.Analysis
