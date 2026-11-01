module

public import KVApproximation.Analysis.PeriodicSobolev
public import KVApproximation.Analysis.VectorSobolevFields
public import TauCeti.Analysis.Sobolev.TestFunctionLp

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Tensor
open scoped Distributions InnerProductSpace Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, oscillating-flux limit: a divergence-free periodic
stress pairs with displacement strains as its cell mean whenever the
displacement values converge strongly in L². -/
theorem tendsto_integral_cutoff_rescale_stress_strain_along {d : ℕ}
    (σ : Lp (Symmetric d) 2 (cellMeasure d))
    (hσ : ∀ w : PeriodicH1 d, ⟪σ, PeriodicH1.symmetricGradientL d w⟫_ℝ = 0)
    {Ω : Opens (PhysicalSpace d)} (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (χ : 𝓓(Ω, ℝ)) {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝[>] (0 : ℝ))) {u : ι → ZeroBoundaryH1 Ω} {u₀ : ZeroBoundaryH1 Ω}
    (hu : Tendsto (fun i => VectorH1.valueL Ω (u i).val) l
      (𝓝 (VectorH1.valueL Ω u₀.val))) :
    Tendsto (fun i => ∫ x in (Ω : Set (PhysicalSpace d)),
      χ x * ⟪rescalePeriodic σ (ε i) x, VectorH1.symmetricGradientL Ω (u i).val x⟫_ℝ)
      l
      (𝓝 (∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * ⟪∫ y, σ y ∂cellMeasure d, VectorH1.symmetricGradientL Ω u₀.val x⟫_ℝ)) := by
  sorry

/-- Theorem 3.1, oscillating-flux limit: a divergence-free periodic
stress pairs with displacement strains as its cell mean whenever the
displacement values converge strongly in L². -/
theorem tendsto_integral_cutoff_rescale_stress_strain {d : ℕ}
    (σ : Lp (Symmetric d) 2 (cellMeasure d))
    (hσ : ∀ w : PeriodicH1 d, ⟪σ, PeriodicH1.symmetricGradientL d w⟫_ℝ = 0)
    {Ω : Opens (PhysicalSpace d)} (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (χ : 𝓓(Ω, ℝ)) {u : ℝ → ZeroBoundaryH1 Ω} {u₀ : ZeroBoundaryH1 Ω}
    (hu : Tendsto (fun ε => VectorH1.valueL Ω (u ε).val) (𝓝[>] (0 : ℝ))
      (𝓝 (VectorH1.valueL Ω u₀.val))) :
    Tendsto (fun ε : ℝ => ∫ x in (Ω : Set (PhysicalSpace d)),
      χ x * ⟪rescalePeriodic σ ε x, VectorH1.symmetricGradientL Ω (u ε).val x⟫_ℝ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * ⟪∫ y, σ y ∂cellMeasure d, VectorH1.symmetricGradientL Ω u₀.val x⟫_ℝ)) := by
  sorry

end KVApproximation.Analysis
