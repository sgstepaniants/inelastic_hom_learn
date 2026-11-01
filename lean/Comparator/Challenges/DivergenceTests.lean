module

public import KVApproximation.Analysis.VectorSobolev
public import TauCeti.Analysis.Sobolev.W1p.Zero

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, static flux tests: a C¹ divergence-free L² vector
field annihilates the weak gradients of all scalar Dirichlet functions. -/
theorem integral_inner_gradient_eq_zero_of_divergence_eq_zero {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} {q : PhysicalSpace d → PhysicalSpace d}
    (hq : ContDiff ℝ 1 q) (hq₂ : MemLp q 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (hdiv : ∀ x ∈ (Ω : Set (PhysicalSpace d)),
      (∑ j, (fderiv ℝ q x (EuclideanSpace.single j 1)) j) = 0)
    (v : TauCeti.W1p volume Ω 2) (hv : v ∈ TauCeti.w1p0Submodule volume Ω 2) :
    (∫ x in (Ω : Set (PhysicalSpace d)), ⟪q x, TauCeti.W1p.gradient v x⟫_ℝ) = 0 := by
  sorry

end KVApproximation.Analysis
