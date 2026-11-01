module

public import KVApproximation.Analysis.PeriodicAveragingReal
public import KVApproximation.Analysis.PeriodicRescaledJetProperties
public import KVApproximation.Analysis.PeriodicGradientMean
public import KVApproximation.Analysis.VectorSobolevProperties

/-!
# Rescaled periodic Sobolev correctors

The smooth chain rule extends through the closed weak-derivative graph.
Uniform L² rescaling bounds control the displacement amplitude, while
periodic averaging identifies the weak limit of its gradient.
-/

public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open KVApproximation.Tensor
open scoped Topology Gradient ENNReal

namespace KVApproximation.Analysis

open PeriodicRescaledJets

/-- Theorem 3.1, oscillating correctors: multiplying a rescaled periodic
L² field by its scale gives strong L² convergence to zero. -/
theorem tendsto_eLpNorm_smul_rescalePeriodic_zero {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (PhysicalSpace d)} (hΩ : Bornology.IsBounded Ω)
    {f : PeriodicCell d → F} (hf : MemLp f 2 (cellMeasure d)) :
    Tendsto (fun ε : ℝ =>
      eLpNorm (fun x => ε • rescalePeriodic f ε x) 2 (volume.restrict Ω))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := exists_eLpNorm_two_rescalePeriodic_bound (F := F) hΩ
  have he : Tendsto (fun ε : ℝ => ‖ε‖ₑ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0)).enorm
  have hfinite : ENNReal.ofReal C * eLpNorm f 2 (cellMeasure d) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_lt_top.ne
  have hlim : Tendsto
      (fun ε : ℝ => ‖ε‖ₑ * (ENNReal.ofReal C * eLpNorm f 2 (cellMeasure d)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul he (Or.inr hfinite) tendsto_const_nhds
      (Or.inr ENNReal.zero_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with ε hε hε₁
  calc
    eLpNorm (fun x => ε • rescalePeriodic f ε x) 2 (volume.restrict Ω) =
        ‖ε‖ₑ * eLpNorm (rescalePeriodic f ε) 2 (volume.restrict Ω) :=
      eLpNorm_const_smul ε (rescalePeriodic f ε) 2 (volume.restrict Ω)
    _ ≤ _ := by
      gcongr
      exact hbound ε hε hε₁.le f hf.aestronglyMeasurable

/-- Theorem 3.1, oscillating corrector tests: the scaled periodic
displacement belongs to physical H¹ and its weak gradient is the
rescaled periodic gradient, with both identities holding almost everywhere. -/
theorem PeriodicH1.exists_rescaled {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (u : PeriodicH1 d) :
    ∃ v : VectorH1 Ω,
      (VectorH1.valueL Ω v =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => ε • rescalePeriodic (PeriodicH1.valueL d u) ε x) ∧
      (VectorH1.gradientL Ω v =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        rescalePeriodic (PeriodicH1.gradientL d u) ε) := by
  obtain ⟨C, _, hbound⟩ := exists_rescaling_measure_bound hΩ
  have hq := (quasiMeasurePreserving_scaledToCell (d := d) hε.ne').measurable
  let R := rescaleJet hq ENNReal.ofReal_ne_top (hbound ε hε hε₁)
  let T (i : Fin d) : PeriodicJetField d →L[ℝ] TauCeti.Sobolev1JetLp volume Ω 2 :=
    ((jetCoordinate ε i).compLpL 2 (volume.restrict (Ω : Set (PhysicalSpace d)))).comp R
  have hT (i : Fin d) (w : PeriodicJetField d) :
      ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
        T i w x = jetCoordinate ε i (w (toCell (ε⁻¹ • x))) := by
    filter_upwards [(jetCoordinate ε i).coeFn_compLpL (R w),
      rescaleJet_ae hq ENNReal.ofReal_ne_top (hbound ε hε hε₁) w] with x ht hr
    change ((jetCoordinate ε i).compLpL 2 (volume.restrict (Ω : Set (PhysicalSpace d)))
      (R w)) x = _
    rw [ht, hr]
    rfl
  have hmem (i : Fin d) : T i u.val ∈ TauCeti.w1pSubmodule volume Ω 2 := by
    let K : ClosedSubmodule ℝ (PeriodicJetField d) :=
      (TauCeti.w1pSubmodule volume Ω 2).comap (T i)
    have hle : periodicH1Submodule d ≤ K := by
      apply Submodule.closure_le.mpr
      apply Submodule.span_le.mpr
      rintro w ⟨φ, hφ, hw⟩
      let ψ : PeriodicC1 d (PhysicalSpace d) := ⟨φ, hφ.of_le (by simp)⟩
      let f : PhysicalSpace d → ℝ := fun x => ε * φ (toCell (ε⁻¹ • x)) i
      have hf : ContDiff ℝ 1 f :=
        contDiff_const.mul
          (((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i).contDiff.comp
            ψ.contDiff_lift).comp
              (ε⁻¹ • ContinuousLinearMap.id ℝ (PhysicalSpace d)).contDiff)
      obtain ⟨v, hv, hg⟩ :=
        TauCeti.W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact
          (mu := volume) (Omega := Ω) (p := 2)
          isOpen_univ hf.contDiffOn hΩ.isCompact_closure subset_closure (Set.subset_univ _)
      have hwr : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
          w (toCell (ε⁻¹ • x)) = WithLp.toLp 2
            (φ (toCell (ε⁻¹ • x)), periodicGradient φ (toCell (ε⁻¹ • x))) :=
        ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hε.ne').ae hw)
      have hTv : T i w = (v : TauCeti.Sobolev1JetLp volume Ω 2) := by
        apply TauCeti.Sobolev1JetLp.ext
        · apply Lp.ext
          filter_upwards [TauCeti.Sobolev1JetLp.value_apply_ae (T i w),
            hT i w, hwr, hv] with x ht hj hwx hvx
          rw [← TauCeti.W1p.value_coe v, ht, hj, hwx, jetCoordinate_apply, hvx]
          rfl
        · apply Lp.ext
          filter_upwards [TauCeti.Sobolev1JetLp.gradient_apply_ae (T i w),
            hT i w, hwr, hg] with x ht hj hwx hgx
          rw [← TauCeti.W1p.gradient_coe v, ht, hj, hwx, jetCoordinate_apply, hgx]
          exact (gradient_scaled_component ψ hε.ne' i x).symm
      change T i w ∈ TauCeti.w1pSubmodule volume Ω 2
      rw [hTv]
      exact v.property
    exact hle u.property
  let v : VectorH1 Ω := WithLp.toLp 2 (fun i => ⟨T i u.val, hmem i⟩)
  have hval : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      PeriodicH1.valueL d u (toCell (ε⁻¹ • x)) = WithLp.fst (u.val (toCell (ε⁻¹ • x))) :=
    ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hε.ne').ae
      ((WithLp.fstL 2 ℝ (PhysicalSpace d) (SecondOrder d)).coeFn_compLpL u.val))
  have hgrad : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      PeriodicH1.gradientL d u (toCell (ε⁻¹ • x)) = WithLp.snd (u.val (toCell (ε⁻¹ • x))) :=
    ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hε.ne').ae
      ((WithLp.sndL 2 ℝ (PhysicalSpace d) (SecondOrder d)).coeFn_compLpL u.val))
  have hv (i : Fin d) : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      TauCeti.W1p.value (v i) x = ε * PeriodicH1.valueL d u (toCell (ε⁻¹ • x)) i := by
    filter_upwards [TauCeti.W1p.value_apply_ae (v i), hT i u.val, hval]
      with x hx ht hu
    change TauCeti.W1p.value (v i) x = _
    rw [hx]
    change WithLp.fst (T i u.val x) = _
    rw [ht, jetCoordinate_apply, hu]
    rfl
  have hg (i : Fin d) : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      TauCeti.W1p.gradient (v i) x =
        WithLp.toLp 2 (fun j => PeriodicH1.gradientL d u (toCell (ε⁻¹ • x)) (i, j)) := by
    filter_upwards [TauCeti.W1p.gradient_apply_ae (v i), hT i u.val, hgrad]
      with x hx ht hu
    rw [hx]
    change WithLp.snd (T i u.val x) = _
    rw [ht, jetCoordinate_apply, hu]
    rfl
  refine ⟨v, ?_, ?_⟩
  · filter_upwards [VectorH1.valueL_apply_ae v, ae_all_iff.mpr hv] with x hx hi
    rw [hx]
    apply PiLp.ext
    intro i
    exact hi i
  · filter_upwards [VectorH1.gradientL_apply_ae v, ae_all_iff.mpr hg] with x hx hi
    rw [hx]
    apply PiLp.ext
    intro ij
    exact congrArg (fun z : PhysicalSpace d => z ij.2) (hi ij.1)

/-- Theorem 3.1, oscillating correctors: periodic gradients converge
weakly to zero after rescaling, since their normalized cell mean is zero. -/
theorem PeriodicH1.tendsto_integral_rescale_gradient_inner {d : ℕ}
    {Ω : Set (PhysicalSpace d)} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) (u : PeriodicH1 d)
    {g : PhysicalSpace d → SecondOrder d} (hg : MemLp g 2 (volume.restrict Ω)) :
    Tendsto (fun ε : ℝ =>
      ∫ x in Ω, inner ℝ (rescalePeriodic (PeriodicH1.gradientL d u) ε x) (g x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [PeriodicH1.integral_gradient_eq_zero u, inner_zero_left] using
    tendsto_integral_rescalePeriodic_inner hΩ hΩm
      (Lp.memLp (PeriodicH1.gradientL d u)) hg

end KVApproximation.Analysis
