module

public import KVApproximation.Analysis.PeriodicStrongTests
public import KVApproximation.Analysis.PeriodicStressRescaling
public import KVApproximation.Analysis.CutoffPairingProperties

/-!
# Localized limits of periodic equilibrium stresses

Testing a divergence-free stress against a cutoff displacement moves the
gradient onto the smooth cutoff. Strong L² convergence of displacement
values then suffices for the oscillating-stress limit.
-/

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Tensor
open scoped Distributions InnerProductSpace Topology

namespace KVApproximation.Analysis

private theorem cutoffPairing_eq_inner_symmetric {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (χ : 𝓓(Ω, ℝ))
    (σ : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (v : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    cutoffPairing χ σ v = ⟪σ, (symmetrizeL d).compLpL 2
      (volume.restrict (Ω : Set (PhysicalSpace d))) (cutoffGradientL χ v)⟫_ℝ := by
  change ⟪(symmetricSubmodule d).subtypeL.compLpL 2
    (volume.restrict (Ω : Set (PhysicalSpace d))) σ, cutoffGradientL χ v⟫_ℝ = _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(symmetricSubmodule d).subtypeL.coeFn_compLpL σ,
    (symmetrizeL d).coeFn_compLpL (cutoffGradientL χ v)] with x hs hv
  rw [hs, hv]
  exact (inner_symmetrize (σ x) (cutoffGradientL χ v x)).symm

set_option maxHeartbeats 400000 in
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
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩ.measure_lt_top.ne
  let T : Lp (PhysicalSpace d) 2 μ →L[ℝ] Lp (Symmetric d) 2 μ :=
    ((symmetrizeL d).compLpL 2 μ).comp (cutoffGradientL χ)
  let m := ∫ y, σ y ∂cellMeasure d
  let S : Lp (Symmetric d) 2 μ := Lp.const 2 μ m
  have hS : S =ᵐ[μ] fun _ => m := Lp.coeFn_const 2 μ m
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with ε hε hε₁
    exact ⟨hε, hε₁.le⟩
  have hSzero (v : ZeroBoundaryH1 Ω) :
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪S x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = 0 := by
    have havg := tendsto_integral_rescalePeriodic_inner hΩ Ω.isOpen.measurableSet
      (Lp.memLp σ) (Lp.memLp (VectorH1.symmetricGradientL Ω v.val))
    have hz : Tendsto (fun ε : ℝ => ∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪rescalePeriodic σ ε x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hsmall] with ε hε
      exact (integral_rescale_stress_strain_eq_zero σ hσ hΩ hε.1 hε.2 v).symm
    calc
      _ = ∫ x in (Ω : Set (PhysicalSpace d)),
          ⟪m, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [hS] with x hx
        rw [hx]
      _ = ⟪m, ∫ x in (Ω : Set (PhysicalSpace d)),
          VectorH1.symmetricGradientL Ω v.val x⟫_ℝ :=
        integral_inner ((Lp.memLp (VectorH1.symmetricGradientL Ω v.val)).integrable
          (by norm_num)) m
      _ = 0 := tendsto_nhds_unique havg hz
  have hT := T.continuous.continuousAt.tendsto.comp hu
  have hlim := tendsto_integral_rescalePeriodic_inner_strong_along hΩ Ω.isOpen.measurableSet
    (Lp.memLp σ) hε hT
  have hmean : ⟪m, ∫ x in (Ω : Set (PhysicalSpace d)), T (VectorH1.valueL Ω u₀.val) x⟫_ℝ =
      cutoffPairing χ S (VectorH1.valueL Ω u₀.val) := by
    rw [cutoffPairing_eq_inner_symmetric, L2.inner_def]
    calc
      _ = ∫ x in (Ω : Set (PhysicalSpace d)),
          ⟪m, T (VectorH1.valueL Ω u₀.val) x⟫_ℝ :=
        (integral_inner ((Lp.memLp (T (VectorH1.valueL Ω u₀.val))).integrable
          (by norm_num)) m).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hS] with x hx
        rw [hx]
        rfl
  have hlast : -⟪m, ∫ x in (Ω : Set (PhysicalSpace d)), T (VectorH1.valueL Ω u₀.val) x⟫_ℝ =
      ∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * ⟪m, VectorH1.symmetricGradientL Ω u₀.val x⟫_ℝ := by
    rw [hmean, ← integral_cutoff_stress_strain_eq_neg_pairing χ S hSzero u₀]
    apply integral_congr_ae
    filter_upwards [hS] with x hx
    rw [hx]
  have hn := hlim.neg
  change Tendsto (fun i => -(∫ x in (Ω : Set (PhysicalSpace d)),
    ⟪rescalePeriodic σ (ε i) x, T (VectorH1.valueL Ω (u i).val) x⟫_ℝ))
    l (𝓝 (-⟪m, ∫ x in (Ω : Set (PhysicalSpace d)),
      T (VectorH1.valueL Ω u₀.val) x⟫_ℝ)) at hn
  rw [hlast] at hn
  apply hn.congr'
  filter_upwards [hε.eventually hsmall] with i hi
  have hr := memLp_two_rescalePeriodic hΩ hi.1 hi.2 (Lp.memLp σ)
  let R := hr.toLp (rescalePeriodic σ (ε i))
  have hR : R =ᵐ[μ] rescalePeriodic σ (ε i) := hr.coeFn_toLp
  have hRzero (v : ZeroBoundaryH1 Ω) :
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪R x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = 0 := by
    calc
      _ = ∫ x in (Ω : Set (PhysicalSpace d)),
          ⟪rescalePeriodic σ (ε i) x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [hR] with x hx
        rw [hx]
      _ = 0 := integral_rescale_stress_strain_eq_zero σ hσ hΩ hi.1 hi.2 v
  symm
  calc
    _ = ∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * ⟪R x, VectorH1.symmetricGradientL Ω (u i).val x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [hR] with x hx
      rw [hx]
    _ = -cutoffPairing χ R (VectorH1.valueL Ω (u i).val) :=
      integral_cutoff_stress_strain_eq_neg_pairing χ R hRzero (u i)
    _ = -⟪R, T (VectorH1.valueL Ω (u i).val)⟫_ℝ := by
      rw [cutoffPairing_eq_inner_symmetric]
      rfl
    _ = _ := by
      congr 1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hR] with x hx
      rw [hx]

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
  exact tendsto_integral_cutoff_rescale_stress_strain_along σ hσ hΩ χ tendsto_id hu

end KVApproximation.Analysis
