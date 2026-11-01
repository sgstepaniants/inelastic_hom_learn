module

public import KVApproximation.Analysis.VectorSobolev
public import TauCeti.Analysis.Sobolev.W1p.Zero

/-!
# Scalar coordinates of zero-boundary displacements
-/

public section

open MeasureTheory TopologicalSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, Dirichlet space: the closure of smooth compactly
supported vector jets is exactly the space whose scalar coordinates
belong to the corresponding scalar zero-boundary Sobolev spaces. -/
theorem mem_zeroBoundary_iff {d : ℕ} {Ω : Opens (PhysicalSpace d)} (u : VectorH1 Ω) :
    u ∈ zeroBoundarySubmodule Ω ↔
      ∀ i : Fin d, u i ∈ TauCeti.w1p0Submodule volume Ω 2 := by
  sorry

/-- Theorem 3.1, Dirichlet space: a nonempty open domain in positive
physical dimension admits a nonzero zero-boundary displacement. -/
theorem ZeroBoundaryH1.exists_ne_zero {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (hd : 0 < d) (hΩ : (Ω : Set (PhysicalSpace d)).Nonempty) :
    ∃ u : ZeroBoundaryH1 Ω, u ≠ 0 := by
  sorry

end KVApproximation.Analysis
