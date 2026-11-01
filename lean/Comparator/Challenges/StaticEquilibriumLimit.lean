module

public import KVApproximation.Homogenization.StaticCellOperators
public import KVApproximation.Homogenization.StaticWeakProblem
public import KVApproximation.Analysis.VectorSobolevFields

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace Topology

namespace KVApproximation.Homogenization

/-- Theorem 3.1, static periodic homogenization: a displacement limit
with strongly convergent values and a weak microscopic stress limit
satisfies the actual effective equilibrium equation. -/
theorem effective_equilibrium_of_weak_stress {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (f : SpatialL2 Ω)
    {ι : Type*} {l : Filter ι} [NeBot l]
    {ε : ι → ℝ} (hε : Tendsto ε l (𝓝[>] (0 : ℝ)))
    {u : ι → ZeroBoundaryH1 Ω} {u₀ : ZeroBoundaryH1 Ω}
    (hu : Tendsto (fun i => VectorH1.valueL Ω (u i).val) l
      (𝓝 (VectorH1.valueL Ω u₀.val)))
    (σ : ι → Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (σ₀ : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (hweak : ∀ ℓ : Lp (Symmetric d) 2
        (volume.restrict (Ω : Set (PhysicalSpace d))) →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (σ i)) l (𝓝 (ℓ σ₀)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ i in l, ‖σ i‖ ≤ C)
    (hσ : ∀ᶠ i in l, σ i =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      action (rescalePeriodic A.field (ε i) x) (VectorH1.symmetricGradientL Ω (u i).val x))
    (heq : ∀ᶠ i in l, ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪σ i x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = loadPairing f v) :
    ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm A (symmetricGradient u₀ x) (symmetricGradient v x)) =
          loadPairing f v := by
  sorry

end KVApproximation.Homogenization
