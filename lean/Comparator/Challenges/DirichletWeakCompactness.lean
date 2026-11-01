module

public import KVApproximation.Analysis.DirichletFields

/-!
# Weak H¹ and strong L² compactness
-/

public section

open MeasureTheory TopologicalSpace Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, static homogenization: a uniformly H¹-bounded sequence
of zero-boundary displacements has a subsequence converging weakly in H¹₀
and strongly in L² to the same zero-boundary displacement. -/
theorem ZeroBoundaryH1.exists_subseq_weak_strong
    {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (u : ℕ → ZeroBoundaryH1 Ω) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ uLim : ZeroBoundaryH1 Ω, ‖uLim‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim))) ∧
      Tendsto (fun n => ZeroBoundaryH1.valueL Ω (u (φ n))) atTop
        (𝓝 (ZeroBoundaryH1.valueL Ω uLim)) := by
  sorry

end KVApproximation.Analysis
