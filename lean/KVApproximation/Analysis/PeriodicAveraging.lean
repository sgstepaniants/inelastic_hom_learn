module

public import KVApproximation.Analysis.PeriodicRescalingLp
public import KVApproximation.Analysis.PeriodicFourierAveraging
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Weak averaging of periodic L² fields

Uniform measure domination gives bounded pullback maps on L². Their
pairings form an equicontinuous family, so Fourier-mode convergence
extends from the dense span of the torus characters to every L² field.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate ENNReal NNReal

namespace KVApproximation.Analysis

section Pullback

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} (q : X → Y) (hq : Measurable q)
  {c : ℝ≥0∞} (hc : c ≠ ⊤) (hbound : μ.map q ≤ c • ν)

private noncomputable def pullbackReal : Lp ℂ 2 ν →L[ℝ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ q (hq.measurePreserving μ)).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul hc hbound)

private theorem pullbackReal_ae (u : Lp ℂ 2 ν) :
    pullbackReal q hq hc hbound u =ᵐ[μ] fun x => u (q x) := by
  exact (Lp.coeFn_compMeasurePreserving
    (Lp.LpToLpOfMeasureLeSMul hc hbound u) (hq.measurePreserving μ)).trans
      ((hq.measurePreserving μ).quasiMeasurePreserving.ae
        (Lp.coeFn_LpToLpOfMeasureLeSMul hc hbound u))

private noncomputable def pullbackComplex : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ where
  toFun := pullbackReal q hq hc hbound
  map_add' := (pullbackReal q hq hc hbound).map_add
  map_smul' a u := by
    apply Lp.ext
    have hsource : ∀ᵐ x ∂μ, (a • u : Lp ℂ 2 ν) (q x) = a • u (q x) :=
      (hq.measurePreserving μ).quasiMeasurePreserving.ae
        ((Measure.absolutelyContinuous_of_le_smul hbound).ae_eq (Lp.coeFn_smul a u))
    filter_upwards [pullbackReal_ae q hq hc hbound (a • u),
      pullbackReal_ae q hq hc hbound u,
      Lp.coeFn_smul a (pullbackReal q hq hc hbound u), hsource] with x h₁ h₂ h₃ h₄
    simp only [RingHom.id_apply]
    rw [h₁, h₃]
    change (a • u : Lp ℂ 2 ν) (q x) = a • pullbackReal q hq hc hbound u x
    rw [h₂, h₄]
  cont := (pullbackReal q hq hc hbound).continuous

private theorem pullbackComplex_ae (u : Lp ℂ 2 ν) :
    pullbackComplex q hq hc hbound u =ᵐ[μ] fun x => u (q x) :=
  pullbackReal_ae q hq hc hbound u

private theorem norm_pullbackComplex_le :
    ‖pullbackComplex q hq hc hbound‖ ≤ c.toReal ^ (1 / (2 : ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (by positivity) _)
  intro u
  change ‖Lp.compMeasurePreserving q (hq.measurePreserving μ)
    (Lp.LpToLpOfMeasureLeSMul hc hbound u)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  have hb : ‖(Lp.LpToLpOfMeasureLeSMul hc hbound : Lp ℂ 2 ν →L[ℝ] Lp ℂ 2 (μ.map q))‖ ≤
      c.toReal ^ (1 / (2 : ℝ)) := by
    simpa [one_div] using Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) hc hbound
  exact ((Lp.LpToLpOfMeasureLeSMul hc hbound).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg u))

end Pullback

private theorem averaging_Lp {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) (u : Lp ℂ 2 (cellMeasure d))
    (g : Lp ℂ 2 (volume.restrict Ω)) :
    Tendsto (fun ε : ℝ => ∫ x in Ω, rescalePeriodic u ε x * g x)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ y, u y ∂cellMeasure d) * ∫ x in Ω, g x)) := by
  classical
  obtain ⟨K, hK, hbound⟩ := exists_rescaling_measure_bound hΩ
  let q (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) := toCell (ε⁻¹ • x)
  have hq (ε : ℝ) : Measurable (q ε) :=
    (quasiMeasurePreserving_toCell d).measurable.comp (measurable_const_smul _)
  let T (ε : ℝ) : Lp ℂ 2 (cellMeasure d) →L[ℂ] Lp ℂ 2 (volume.restrict Ω) :=
    if h : 0 < ε ∧ ε ≤ 1 then
      pullbackComplex (q ε) (hq ε) ENNReal.ofReal_ne_top (hbound ε h.1 h.2)
    else 0
  have hTnorm (ε : ℝ) : ‖T ε‖ ≤ Real.sqrt K := by
    dsimp only [T]
    split_ifs with h
    · simpa [ENNReal.toReal_ofReal hK.le, Real.sqrt_eq_rpow] using
        norm_pullbackComplex_le (q ε) (hq ε) ENNReal.ofReal_ne_top (hbound ε h.1 h.2)
    · simp
  let F (ε : ℝ) : Lp ℂ 2 (cellMeasure d) →L[ℂ] ℂ :=
    (innerSL ℂ (star g)).comp (T ε)
  let b (n : Fin d → ℤ) : Lp ℂ 2 (cellMeasure d) := UnitAddTorus.mFourierLp 2 n
  let M : Lp ℂ 2 (cellMeasure d) →L[ℂ] ℂ :=
    (∫ x in Ω, g x) • innerSL ℂ (b 0)
  have hFval (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (v : Lp ℂ 2 (cellMeasure d)) :
      F ε v = ∫ x in Ω, rescalePeriodic v ε x * g x := by
    have hTv : T ε v =ᵐ[volume.restrict Ω] rescalePeriodic v ε := by
      dsimp only [T]
      rw [dite_eq_left hε]
      exact pullbackComplex_ae (q ε) (hq ε) ENNReal.ofReal_ne_top
        (hbound ε hε.1 hε.2) v
    change inner ℂ (star g) (T ε v) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hTv, Lp.coeFn_star g] with x hx hg
    simp [RCLike.inner_apply, hx, hg]
  have hMval (v : Lp ℂ 2 (cellMeasure d)) :
      M v = (∫ y, v y ∂cellMeasure d) * ∫ x in Ω, g x := by
    change (∫ x in Ω, g x) * inner ℂ (b 0) v = _
    have hi : inner ℂ (b 0) v = ∫ y, v y ∂cellMeasure d := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [UnitAddTorus.coeFn_mFourierLp (d := Fin d) 2 0] with y hy
      change inner ℂ (UnitAddTorus.mFourierLp 2 0 y) (v y) = v y
      rw [hy]
      simp [UnitAddTorus.mFourier_zero]
    rw [hi, mul_comm]
  let L : ℝ≥0 := ⟨‖innerSL ℂ (star g)‖ * Real.sqrt K, by positivity⟩
  have hFnorm (ε : ℝ) : ‖F ε‖ ≤ (L : ℝ) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hTnorm ε) (norm_nonneg _))
  have hFequi : Equicontinuous (fun ε : ℝ => fun v : Lp ℂ 2 (cellMeasure d) => F ε v) :=
    (LipschitzWith.uniformEquicontinuous _ L fun ε =>
      (F ε).lipschitzWith.weaken (by exact_mod_cast hFnorm ε)).equicontinuous
  let S : Submodule ℂ (Lp ℂ 2 (cellMeasure d)) := {
    carrier := {v | Tendsto (fun ε : ℝ => F ε v) (𝓝[>] (0 : ℝ)) (𝓝 (M v))}
    zero_mem' := by simp
    add_mem' {v w} hv hw := by
      change Tendsto (fun ε : ℝ => F ε (v + w)) (𝓝[>] (0 : ℝ)) (𝓝 (M (v + w)))
      simpa only [map_add] using hv.add hw
    smul_mem' a v hv := by
      change Tendsto (fun ε : ℝ => F ε (a • v)) (𝓝[>] (0 : ℝ)) (𝓝 (M (a • v)))
      simpa only [map_smul] using hv.const_smul a }
  have hSclosed : IsClosed (S : Set (Lp ℂ 2 (cellMeasure d))) :=
    hFequi.isClosed_setOfPred_tendsto M.continuous
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with ε hε hε₁
    exact ⟨hε, hε₁.le⟩
  have hmode (n : Fin d → ℤ) : b n ∈ S := by
    have hm := tendsto_integral_rescale_mFourier_mul n (Ω.indicator g)
    have hlim : (if n = 0 then ∫ x, Ω.indicator g x else 0) = M (b n) := by
      rw [integral_indicator hΩm]
      change (if n = 0 then ∫ x in Ω, g x else 0) =
        (∫ x in Ω, g x) * inner ℂ (b 0) (b n)
      have hi : inner ℂ (b 0) (b n) = if (0 : Fin d → ℤ) = n then 1 else 0 :=
        orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d)) 0 n
      rw [hi]
      by_cases hn : n = 0 <;> simp [hn, eq_comm]
    rw [hlim] at hm
    apply hm.congr'
    filter_upwards [hsmall] with ε hε
    symm
    rw [hFval ε hε]
    calc
      (∫ x in Ω, rescalePeriodic (b n) ε x * g x) =
          ∫ x in Ω, rescalePeriodic (UnitAddTorus.mFourier n) ε x * g x := by
        apply integral_congr_ae
        have ha := (quasiMeasurePreserving_scaledToCell (d := d) hε.1.ne').ae
          (UnitAddTorus.coeFn_mFourierLp (d := Fin d) 2 n)
        filter_upwards [ae_restrict_of_ae ha] with x hx
        exact congrArg (fun z => z * g x) hx
      _ = ∫ x, rescalePeriodic (UnitAddTorus.mFourier n) ε x * Ω.indicator g x := by
        rw [← integral_indicator hΩm]
        congr 1
        funext x
        by_cases hx : x ∈ Ω <;> simp [hx]
  have hspan : Submodule.span ℂ (Set.range b) ≤ S :=
    Submodule.span_le.mpr fun v ⟨n, hn⟩ => hn ▸ hmode n
  have htop := (Submodule.span ℂ (Set.range b)).topologicalClosure_minimal hspan hSclosed
  have hclosure : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤ :=
    UnitAddTorus.span_mFourierLp_closure_eq_top (d := Fin d) (by norm_num)
  rw [hclosure] at htop
  have hu : u ∈ S := htop (Submodule.mem_top)
  change Tendsto (fun ε : ℝ => F ε u) (𝓝[>] (0 : ℝ)) (𝓝 (M u)) at hu
  rw [hMval] at hu
  apply hu.congr'
  filter_upwards [hsmall] with ε hε
  exact hFval ε hε u

/-- Theorem 3.1, static periodic homogenization: every periodic L² field
converges weakly on a bounded measurable physical domain to its cell mean.
The test is an arbitrary physical L² function. -/
theorem tendsto_integral_rescalePeriodic_mul {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) {f : PeriodicCell d → ℂ}
    (hf : MemLp f 2 (cellMeasure d)) {g : EuclideanSpace ℝ (Fin d) → ℂ}
    (hg : MemLp g 2 (volume.restrict Ω)) :
    Tendsto (fun ε : ℝ => ∫ x in Ω, rescalePeriodic f ε x * g x)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ y, f y ∂cellMeasure d) * ∫ x in Ω, g x)) := by
  have h := averaging_Lp hΩ hΩm (hf.toLp f) (hg.toLp g)
  have hfi : (∫ y, hf.toLp f y ∂cellMeasure d) = ∫ y, f y ∂cellMeasure d :=
    integral_congr_ae hf.coeFn_toLp
  have hgi : (∫ x in Ω, hg.toLp g x) = ∫ x in Ω, g x :=
    integral_congr_ae hg.coeFn_toLp
  rw [hfi, hgi] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  have hfr := (quasiMeasurePreserving_scaledToCell (d := d) (ne_of_gt hε)).ae hf.coeFn_toLp
  filter_upwards [ae_restrict_of_ae hfr, hg.coeFn_toLp] with x hfx hgx
  exact congrArg₂ (· * ·) hfx hgx

end KVApproximation.Analysis
