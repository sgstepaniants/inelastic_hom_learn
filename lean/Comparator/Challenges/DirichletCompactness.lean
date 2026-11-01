module

public import KVApproximation.Analysis.DirichletFields
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness of zero-boundary displacements
-/

public section

open MeasureTheory TopologicalSpace Filter
open scoped Topology

namespace KVApproximation.Analysis

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, static homogenization: on every bounded open domain,
the actual value map from vector H¹₀ to vector L² is compact. -/
theorem ZeroBoundaryH1.isCompactOperator_valueL
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    IsCompactOperator (ZeroBoundaryH1.valueL Ω) := by
  sorry

/-- Theorem 3.1, static homogenization: an H¹-bounded set of
zero-boundary displacements has relatively compact L² values. -/
theorem ZeroBoundaryH1.isCompact_closure_value_image
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {S : Set (ZeroBoundaryH1 Ω)} (hS : Bornology.IsBounded S) :
    IsCompact (closure ((ZeroBoundaryH1.valueL Ω) '' S)) := by
  sorry

/-- Theorem 3.1, static homogenization: every uniformly H¹-bounded
sequence of zero-boundary displacements has a strongly L²-convergent subsequence. -/
theorem ZeroBoundaryH1.exists_subseq_tendsto_value
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (u : ℕ → ZeroBoundaryH1 Ω) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => ZeroBoundaryH1.valueL Ω (u (φ n))) atTop (𝓝 v) := by
  sorry

/-- Theorem 3.1, static homogenization: a uniformly H¹-bounded
sequence converging weakly in H¹₀ converges strongly in L² to the same displacement. -/
theorem ZeroBoundaryH1.tendsto_value_of_weak
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (u : ℕ → ZeroBoundaryH1 Ω) (uLim : ZeroBoundaryH1 Ω)
    {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ uLim))) :
    Tendsto (fun n => ZeroBoundaryH1.valueL Ω (u n)) atTop
      (𝓝 (ZeroBoundaryH1.valueL Ω uLim)) := by
  sorry

end KVApproximation.Analysis
