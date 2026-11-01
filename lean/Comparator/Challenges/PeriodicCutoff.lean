module

public import KVApproximation.Analysis.PeriodicSobolev
public import KVApproximation.Analysis.VectorSobolevProperties
public import KVApproximation.Analysis.ZeroBoundaryCoordinates

public section

open MeasureTheory TopologicalSpace
open scoped Distributions Gradient

namespace KVApproximation.Analysis

/-- Theorem 3.1, oscillating static tests: a scalar compactly supported
cutoff of the scaled periodic corrector is an actual Dirichlet displacement,
with the full weak-gradient product rule. -/
theorem PeriodicH1.exists_rescaled_cutoff {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (χ : 𝓓(Ω, ℝ)) (u : PeriodicH1 d) :
    ∃ v : ZeroBoundaryH1 Ω,
      (VectorH1.valueL Ω v.val =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => χ x • (ε • rescalePeriodic (PeriodicH1.valueL d u) ε x)) ∧
      (VectorH1.gradientL Ω v.val =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => WithLp.toLp 2 (fun ij =>
          χ x * rescalePeriodic (PeriodicH1.gradientL d u) ε x ij +
          (ε * rescalePeriodic (PeriodicH1.valueL d u) ε x ij.1) *
            (∇ (χ : PhysicalSpace d → ℝ) x) ij.2)) := by
  sorry

end KVApproximation.Analysis
