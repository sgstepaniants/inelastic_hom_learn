module

public import KVApproximation.Analysis.PeriodicSobolev
public import KVApproximation.Analysis.PeriodicRescaling
public import KVApproximation.Analysis.VectorSobolevFields

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, static oscillating fluxes: a periodic symmetric stress
orthogonal to all periodic strains remains orthogonal to all physical
Dirichlet strains after rescaling. -/
theorem integral_rescale_stress_strain_eq_zero {d : ℕ}
    (σ : Lp (Symmetric d) 2 (cellMeasure d))
    (hσ : ∀ w : PeriodicH1 d, ⟪σ, PeriodicH1.symmetricGradientL d w⟫_ℝ = 0)
    {Ω : Opens (PhysicalSpace d)} (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (v : ZeroBoundaryH1 Ω) :
    (∫ x in (Ω : Set (PhysicalSpace d)),
      ⟪rescalePeriodic σ ε x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = 0 := by
  sorry

end KVApproximation.Analysis
