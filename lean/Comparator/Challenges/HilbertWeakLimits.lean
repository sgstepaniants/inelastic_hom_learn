module

public import Mathlib.Analysis.InnerProductSpace.Dual

public section

open Filter
open scoped Topology NNReal

namespace KVApproximation.Analysis

/-- Theorem 3.1, uniform bounds in the limit: an eventual Hilbert-norm
bound passes through weak convergence along every nontrivial filter. -/
theorem norm_le_of_weak_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {I : Type*} {l : Filter I} [NeBot l]
    (u : I → H) (uLim : H) {C : ℝ}
    (hu : ∀ ℓ : H →L[ℝ] ℝ, Tendsto (fun i => ℓ (u i)) l (𝓝 (ℓ uLim)))
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C) : ‖uLim‖ ≤ C := by
  sorry

/-- Theorem 3.1, Green-operator construction: a pointwise weak limit
of uniformly bounded linear operators is a bounded linear operator with
the same norm bound. Neither space needs to be complete. -/
theorem exists_continuousLinearMap_of_weak_tendsto
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {I : Type*} {l : Filter I} [NeBot l]
    (A : I → E →L[ℝ] H) (f : E → H) {C : ℝ}
    (hweak : ∀ x : E, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (A i x)) l (𝓝 (ℓ (f x))))
    (hbound : ∀ᶠ i in l, ‖A i‖ ≤ C) :
    ∃ B : E →L[ℝ] H, (∀ x : E, B x = f x) ∧ ‖B‖ ≤ C := by
  sorry

/-- Theorem 3.1, regularity of Green limits: a common Lipschitz bound
passes through pointwise weak convergence on any subset of a metric domain.
The subset may be empty and the bound may be zero. -/
theorem lipschitzOnWith_of_weak_tendsto
    {X H : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {I : Type*} {l : Filter I} [NeBot l] (s : Set X)
    (u : I → X → H) (v : X → H) (K : ℝ≥0)
    (hweak : ∀ x ∈ s, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (u i x)) l (𝓝 (ℓ (v x))))
    (hbound : ∀ᶠ i in l, LipschitzOnWith K (u i) s) :
    LipschitzOnWith K v s := by
  sorry

end KVApproximation.Analysis
