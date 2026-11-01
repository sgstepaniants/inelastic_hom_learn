module

public import KVApproximation.Analysis.TimeSobolev

public section

open Filter
open scoped Topology

namespace KVApproximation.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, time-space compactness: a bounded sequence in the actual
finite-time H¹ space has a weakly convergent subsequence with the same norm bound. -/
theorem TimeH1.exists_weakly_convergent_subsequence {T : ℝ}
    (u : ℕ → TimeH1 H T) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ uLim : TimeH1 H T, ‖uLim‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  sorry

/-- Theorem 3.1, compatibility of time-space limits: weak H¹ convergence
gives weak convergence of the continuous trace at every time, including both endpoints. -/
theorem TimeH1.weak_trace_tendsto {I : Type*} {l : Filter I} {T : ℝ}
    (hT : 0 < T) (u : I → TimeH1 H T) (uLim : TimeH1 H T)
    (hu : ∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (u i)) l (𝓝 (ℓ uLim)))
    (t : Set.Icc (0 : ℝ) T) (ℓ : H →L[ℝ] ℝ) :
    Tendsto (fun i => ℓ (TimeH1.trace hT (u i) t)) l
      (𝓝 (ℓ (TimeH1.trace hT uLim t))) := by
  sorry

end KVApproximation.Analysis
