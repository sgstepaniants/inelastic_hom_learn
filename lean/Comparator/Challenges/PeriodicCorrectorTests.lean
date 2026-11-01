module

public import KVApproximation.Analysis.PeriodicSobolev
public import KVApproximation.Analysis.VectorSobolevFields
public import TauCeti.Analysis.Sobolev.TestFunctionLp

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Tensor
open scoped Distributions InnerProductSpace Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, microscopic equilibrium tested by oscillating
correctors along a scale map tending to zero: a bounded equilibrium
stress has vanishing localized corrector-strain pairing. -/
theorem tendsto_integral_cutoff_stress_corrector_zero_along {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (χ : 𝓓(Ω, ℝ)) (w : PeriodicH1 d)
    (f : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] (0 : ℝ)))
    (σ : ι → Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ i in l, ‖σ i‖ ≤ C)
    (heq : ∀ᶠ i in l, ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪σ i x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) =
          ⟪f, VectorH1.valueL Ω v.val⟫_ℝ) :
    Tendsto (fun i => ∫ x in (Ω : Set (PhysicalSpace d)),
      χ x * ⟪σ i x, rescalePeriodic (PeriodicH1.symmetricGradientL d w) (ε i) x⟫_ℝ)
      l (𝓝 0) := by
  sorry

/-- Theorem 3.1, microscopic equilibrium tested by oscillating
correctors: a uniformly L²-bounded equilibrium stress has vanishing
localized pairing with every rescaled periodic corrector strain. -/
theorem tendsto_integral_cutoff_stress_corrector_zero {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (χ : 𝓓(Ω, ℝ)) (w : PeriodicH1 d)
    (f : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (σ : ℝ → Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ‖σ ε‖ ≤ C)
    (heq : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪σ ε x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) =
          ⟪f, VectorH1.valueL Ω v.val⟫_ℝ) :
    Tendsto (fun ε : ℝ => ∫ x in (Ω : Set (PhysicalSpace d)),
      χ x * ⟪σ ε x, rescalePeriodic (PeriodicH1.symmetricGradientL d w) ε x⟫_ℝ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry

end KVApproximation.Analysis
