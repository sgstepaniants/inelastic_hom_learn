module

public import KVApproximation.Analysis.PeriodicCutoff
public import KVApproximation.Analysis.PeriodicCorrectorRescaling
public import KVApproximation.Analysis.CutoffPairingProperties

/-!
# Equilibrium tested by periodic correctors

The localized scaled corrector is a genuine Dirichlet test. Its value
converges strongly to zero, leaving only the localized corrector-strain
pairing after the load and cutoff-gradient terms vanish.
-/

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Tensor
open scoped Distributions Gradient InnerProductSpace Topology

namespace KVApproximation.Analysis

set_option maxHeartbeats 400000 in
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
  classical
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  let a := TauCeti.testFunctionLp (mu := volume) ⊤ χ
  let V : Lp (PhysicalSpace d) 2 μ →L[ℝ] Lp (PhysicalSpace d) 2 μ :=
    (ContinuousLinearMap.lsmul ℝ ℝ (E := PhysicalSpace d)).holderL μ ⊤ 2 2 a
  let Z (ε : ℝ) : Lp (PhysicalSpace d) 2 μ :=
    if h : 0 < ε ∧ ε ≤ 1 then
      ((memLp_two_rescalePeriodic hΩ h.1 h.2
        (Lp.memLp (PeriodicH1.valueL d w))).const_smul ε).toLp
          (fun x => ε • rescalePeriodic (PeriodicH1.valueL d w) ε x)
    else 0
  have hZ (ε : ℝ) (h : 0 < ε ∧ ε ≤ 1) :
      Z ε =ᵐ[μ] fun x => ε • rescalePeriodic (PeriodicH1.valueL d w) ε x := by
    dsimp only [Z]
    rw [dite_eq_left h]
    exact MemLp.coeFn_toLp _
  have hV (z : Lp (PhysicalSpace d) 2 μ) : V z =ᵐ[μ] fun x => χ x • z x := by
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := PhysicalSpace d)).coeFn_holder
      (r := 2) a z, TauCeti.testFunctionLp_apply_ae (mu := volume) ⊤ χ] with x hx hχ
    change (ContinuousLinearMap.lsmul ℝ ℝ (E := PhysicalSpace d)).holder 2 a z x = _
    rw [hx]
    change a x • z x = _
    rw [hχ]
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with ε hε hε₁
    exact ⟨hε, hε₁.le⟩
  have hZlim : Tendsto Z (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_eLpNorm_smul_rescalePeriodic_zero hΩ (Lp.memLp (PeriodicH1.valueL d w)))
    simp only [ENNReal.toReal_zero] at h
    apply h.congr'
    filter_upwards [hsmall] with ε hε
    dsimp only [Z]
    rw [dite_eq_left hε, Lp.norm_toLp]
    rfl
  have hZalong := hZlim.comp hε
  have hload : Tendsto (fun i => ⟪f, V (Z (ε i))⟫_ℝ) l (𝓝 0) := by
    have h := ((innerSL ℝ f).comp V).continuous.continuousAt.tendsto.comp hZalong
    change Tendsto (fun i => ⟪f, V (Z (ε i))⟫_ℝ) _ (𝓝 (⟪f, V 0⟫_ℝ)) at h
    simpa only [map_zero, inner_zero_right] using h
  have herr : Tendsto (fun i => cutoffPairing χ (σ i) (Z (ε i))) l (𝓝 0) := by
    have hgradlim := (cutoffGradientL χ).continuous.continuousAt.tendsto.comp hZalong
    change Tendsto (fun i => cutoffGradientL χ (Z (ε i))) _
      (𝓝 (cutoffGradientL χ 0)) at hgradlim
    simp only [map_zero] at hgradlim
    apply squeeze_zero_norm' (a := fun i => C * ‖cutoffGradientL χ (Z (ε i))‖)
    · filter_upwards [hbound] with i hi
      have hs : ‖(symmetricSubmodule d).subtypeL.compLpL 2 μ (σ i)‖ ≤ ‖σ i‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [(symmetricSubmodule d).subtypeL.coeFn_compLpL (σ i)] with x hx
        rw [hx]
        exact le_rfl
      change ‖⟪(symmetricSubmodule d).subtypeL.compLpL 2 μ (σ i),
        cutoffGradientL χ (Z (ε i))⟫_ℝ‖ ≤ _
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hs.trans hi) le_rfl (norm_nonneg _) hC)
    · simpa only [norm_zero, mul_zero] using hgradlim.norm.const_mul C
  have hlim := hload.sub herr
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [hε.eventually hsmall, heq] with i hi heqi
  obtain ⟨v, hv, hgrad⟩ := PeriodicH1.exists_rescaled_cutoff hΩ hi.1 hi.2 χ w
  have hmemG := memLp_two_rescalePeriodic hΩ hi.1 hi.2 (Lp.memLp (PeriodicH1.gradientL d w))
  let G := hmemG.toLp (rescalePeriodic (PeriodicH1.gradientL d w) (ε i))
  have hG : G =ᵐ[μ] rescalePeriodic (PeriodicH1.gradientL d w) (ε i) := hmemG.coeFn_toLp
  have hv' : VectorH1.valueL Ω v.val = V (Z (ε i)) := by
    apply Lp.ext
    filter_upwards [hv, hV (Z (ε i)), hZ (ε i) hi] with x hx hy hz
    rw [hx, hy, hz]
  have hgrad' : VectorH1.gradientL Ω v.val =ᵐ[μ] fun x =>
      WithLp.toLp 2 (fun ij => χ x * G x ij +
        Z (ε i) x ij.1 * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2) := by
    filter_upwards [hgrad, hG, hZ (ε i) hi] with x hx hg hz
    rw [hx, hg, hz]
    rfl
  have hlocal := integral_stress_cutoff_gradient χ (σ i) (Z (ε i)) G v.val hgrad'
  rw [heqi v, hv'] at hlocal
  have hstrain : ∀ᵐ x ∂μ,
      rescalePeriodic (PeriodicH1.symmetricGradientL d w) (ε i) x =
        symmetrize (rescalePeriodic (PeriodicH1.gradientL d w) (ε i) x) :=
    ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hi.1.ne').ae
      ((symmetrizeL d).coeFn_compLpL (PeriodicH1.gradientL d w)))
  have hmain :
      (∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * ⟪σ i x, rescalePeriodic (PeriodicH1.symmetricGradientL d w) (ε i) x⟫_ℝ) =
      ∫ x in (Ω : Set (PhysicalSpace d)), χ x * ⟪(σ i x).val, G x⟫_ℝ := by
    apply integral_congr_ae
    filter_upwards [hstrain, hG] with x hs hg
    rw [hs, inner_symmetrize, hg]
  rw [hmain]
  linarith

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
  exact tendsto_integral_cutoff_stress_corrector_zero_along hΩ χ w f tendsto_id σ
    hC hbound heq

end KVApproximation.Analysis
