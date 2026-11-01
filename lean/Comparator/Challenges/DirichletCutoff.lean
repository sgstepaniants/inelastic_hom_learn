module

public import KVApproximation.Analysis.VectorSobolevProperties
public import KVApproximation.Analysis.ZeroBoundaryCoordinates

public section

open MeasureTheory TopologicalSpace
open scoped Distributions Gradient

namespace KVApproximation.Analysis

/-- Theorem 3.1, localized static tests: multiplication by a smooth
compactly supported scalar preserves the vector Dirichlet space and
has the full gradient product rule in physical coordinates. -/
theorem ZeroBoundaryH1.exists_cutoff {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (χ : 𝓓(Ω, ℝ)) (u : ZeroBoundaryH1 Ω) :
    ∃ v : ZeroBoundaryH1 Ω,
      (VectorH1.valueL Ω v.val =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => χ x • VectorH1.valueL Ω u.val x) ∧
      (VectorH1.gradientL Ω v.val =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => WithLp.toLp 2 (fun ij => χ x * VectorH1.gradientL Ω u.val x ij +
          VectorH1.valueL Ω u.val x ij.1 * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2)) := by
  sorry

end KVApproximation.Analysis
