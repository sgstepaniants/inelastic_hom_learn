module

public import KVApproximation.Homogenization.StaticCellOperators
public import KVApproximation.Homogenization.StaticWeakProblem
public import KVApproximation.Analysis.VectorSobolevFields
public import TauCeti.Analysis.Sobolev.TestFunctionLp

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Analysis KVApproximation.Tensor
open scoped Distributions InnerProductSpace Topology

namespace KVApproximation.Homogenization

/-- Theorem 3.1, static periodic homogenization: the two oscillating
tests identify every localized constant-strain pairing of the microscopic
stress with the actual effective cell form. -/
theorem tendsto_integral_cutoff_microscopic_stress {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (f : SpatialL2 Ω)
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] (0 : ℝ)))
    {u : ι → ZeroBoundaryH1 Ω} {u₀ : ZeroBoundaryH1 Ω}
    (hu : Tendsto (fun i => VectorH1.valueL Ω (u i).val) l
      (𝓝 (VectorH1.valueL Ω u₀.val)))
    (σ : ι → Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ i in l, ‖σ i‖ ≤ C)
    (hσ : ∀ᶠ i in l, σ i =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      action (rescalePeriodic A.field (ε i) x) (VectorH1.symmetricGradientL Ω (u i).val x))
    (heq : ∀ᶠ i in l, ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪σ i x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = loadPairing f v)
    (χ : 𝓓(Ω, ℝ)) (e : Symmetric d) :
    Tendsto (fun i => ∫ x in (Ω : Set (PhysicalSpace d)), χ x * ⟪σ i x, e⟫_ℝ) l
      (𝓝 (∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * effectiveForm A (VectorH1.symmetricGradientL Ω u₀.val x) e)) := by
  sorry

end KVApproximation.Homogenization
