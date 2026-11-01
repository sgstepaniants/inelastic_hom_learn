module

public import KVApproximation.Homogenization.StaticStressIdentification
public import KVApproximation.Analysis.L2TestFunctions
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Effective equilibrium of a compactness limit

Localized smooth tests identify the weak stress limit with the Riesz
representative of the effective cell form. Fixed Dirichlet strain tests
then pass the microscopic equilibrium equation to the limit.
-/

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Analysis KVApproximation.Tensor
open scoped Distributions InnerProductSpace Topology

namespace KVApproximation.Homogenization

set_option maxHeartbeats 400000 in
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
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  let Q := InnerProductSpace.continuousLinearMapOfBilin (effectiveForm A)
  let S := Q.compLpL 2 μ (VectorH1.symmetricGradientL Ω u₀.val)
  have hS : S =ᵐ[μ] fun x => Q (VectorH1.symmetricGradientL Ω u₀.val x) :=
    Q.coeFn_compLpL (VectorH1.symmetricGradientL Ω u₀.val)
  have hQ (g e : Symmetric d) : ⟪Q g, e⟫_ℝ = effectiveForm A g e :=
    InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _
  have hstress : σ₀ = S := by
    apply eq_of_integral_testFunction_inner_eq
    intro χ e
    let a := TauCeti.testFunctionLp (mu := volume) 2 χ
    let z := (ContinuousLinearMap.toSpanSingleton ℝ e).compLpL 2 μ a
    have hz : z =ᵐ[μ] fun x => χ x • e := by
      filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ e).coeFn_compLpL a,
        TauCeti.testFunctionLp_apply_ae (mu := volume) 2 χ] with x hx hχ
      change (ContinuousLinearMap.toSpanSingleton ℝ e).compLpL 2 μ a x = _
      rw [hx]
      change a x • e = _
      rw [hχ]
    have hp (r : Lp (Symmetric d) 2 μ) :
        ⟪z, r⟫_ℝ = ∫ x in (Ω : Set (PhysicalSpace d)), χ x * ⟪r x, e⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hz] with x hx
      rw [hx, real_inner_smul_left e (r x) (χ x)]
      exact congrArg (χ x * ·) (real_inner_comm (r x) e)
    have htest := hweak (innerSL ℝ z)
    change Tendsto (fun i => ⟪z, σ i⟫_ℝ) l (𝓝 ⟪z, σ₀⟫_ℝ) at htest
    simp only [hp] at htest
    have hidentified := tendsto_integral_cutoff_microscopic_stress A hΩ f hε hu σ
      hC hbound hσ heq χ e
    calc
      _ = ∫ x in (Ω : Set (PhysicalSpace d)),
          χ x * effectiveForm A (VectorH1.symmetricGradientL Ω u₀.val x) e :=
        tendsto_nhds_unique htest hidentified
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hS] with x hx
        rw [hx, hQ]
  intro v
  let g := VectorH1.symmetricGradientL Ω v.val
  have hvlim := hweak (innerSL ℝ g)
  change Tendsto (fun i => ⟪g, σ i⟫_ℝ) l (𝓝 ⟪g, σ₀⟫_ℝ) at hvlim
  have hload : Tendsto (fun i => ⟪g, σ i⟫_ℝ) l (𝓝 (loadPairing f v)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with i hi
    calc
      loadPairing f v = ∫ x in (Ω : Set (PhysicalSpace d)), ⟪σ i x, g x⟫_ℝ :=
        (hi v).symm
      _ = ⟪σ i, g⟫_ℝ := (L2.inner_def _ _).symm
      _ = ⟪g, σ i⟫_ℝ := real_inner_comm g (σ i)
  have heffective :
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm A (symmetricGradient u₀ x) (symmetricGradient v x)) = ⟪S, g⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hS, symmetricGradientL_apply_ae u₀, symmetricGradientL_apply_ae v]
      with x hx hu₀ hv
    change effectiveForm A (symmetricGradient u₀ x) (symmetricGradient v x) =
      ⟪S x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ
    rw [hx, hQ, hu₀, hv]
  calc
    _ = ⟪S, g⟫_ℝ := heffective
    _ = ⟪g, σ₀⟫_ℝ := by rw [hstress]; exact real_inner_comm g S
    _ = loadPairing f v := tendsto_nhds_unique hvlim hload

end KVApproximation.Homogenization
