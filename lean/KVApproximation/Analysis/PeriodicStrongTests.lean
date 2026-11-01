module

public import KVApproximation.Analysis.PeriodicAveragingReal

/-!
# Periodic averaging with varying strong tests

Uniform L² rescaling bounds control the difference from the limiting
test. The fixed-test term is the periodic weak-averaging theorem.
-/

public section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, localized oscillating tests: periodic weak averaging
persists when the physical L² test field converges strongly. -/
theorem tendsto_integral_rescalePeriodic_inner_strong_along {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) {f : PeriodicCell d → F}
    (hf : MemLp f 2 (cellMeasure d))
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝[>] (0 : ℝ)))
    {g : ι → Lp F 2 (volume.restrict Ω)} {g₀ : Lp F 2 (volume.restrict Ω)}
    (hg : Tendsto g l (𝓝 g₀)) :
    Tendsto (fun i => ∫ x in Ω, inner ℝ (rescalePeriodic f (ε i) x) (g i x))
      l
      (𝓝 (inner ℝ (∫ y, f y ∂cellMeasure d) (∫ x in Ω, g₀ x))) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_eLpNorm_two_rescalePeriodic_bound (F := F) hΩ
  let R (ε : ℝ) : Lp F 2 (volume.restrict Ω) :=
    if h : 0 < ε ∧ ε ≤ 1 then
      (memLp_two_rescalePeriodic hΩ h.1 h.2 hf).toLp (rescalePeriodic f ε)
    else 0
  have hR (ε : ℝ) (h : 0 < ε ∧ ε ≤ 1) :
      R ε =ᵐ[volume.restrict Ω] rescalePeriodic f ε := by
    dsimp only [R]
    rw [dite_eq_left h]
    exact MemLp.coeFn_toLp _
  have hnorm (ε : ℝ) (h : 0 < ε ∧ ε ≤ 1) :
      ‖R ε‖ ≤ C * (eLpNorm f 2 (cellMeasure d)).toReal := by
    dsimp only [R]
    rw [dite_eq_left h, Lp.norm_toLp]
    have hb := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top)
      (hbound ε h.1 h.2 f hf.aestronglyMeasurable)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] using hb
  have hsmall₀ : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with ε hε hε₁
    exact ⟨hε, hε₁.le⟩
  have hsmall := hε.eventually hsmall₀
  have herr : Tendsto (fun i => ⟪R (ε i), g i - g₀⟫_ℝ) l (𝓝 0) := by
    apply squeeze_zero_norm'
      (a := fun i => (C * (eLpNorm f 2 (cellMeasure d)).toReal) * ‖g i - g₀‖)
    · filter_upwards [hsmall] with i hi
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hnorm (ε i) hi) (norm_nonneg _))
    · simpa using (hg.sub (tendsto_const_nhds (x := g₀))).norm.const_mul
        (C * (eLpNorm f 2 (cellMeasure d)).toReal)
  have hfixed := (tendsto_integral_rescalePeriodic_inner hΩ hΩm hf (Lp.memLp g₀)).comp hε
  have hsum := herr.add hfixed
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hsmall] with i hi
  have hp (v : Lp F 2 (volume.restrict Ω)) :
      ⟪R (ε i), v⟫_ℝ = ∫ x in Ω, ⟪rescalePeriodic f (ε i) x, v x⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hR (ε i) hi] with x hx
    rw [hx]
  simp only [Function.comp_apply]
  rw [← hp g₀, inner_sub_right, sub_add_cancel, hp]

/-- Theorem 3.1, localized oscillating tests: periodic weak averaging
persists when the physical L² test field converges strongly. -/
theorem tendsto_integral_rescalePeriodic_inner_strong {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) {f : PeriodicCell d → F}
    (hf : MemLp f 2 (cellMeasure d))
    {g : ℝ → Lp F 2 (volume.restrict Ω)} {g₀ : Lp F 2 (volume.restrict Ω)}
    (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 g₀)) :
    Tendsto (fun ε : ℝ => ∫ x in Ω, inner ℝ (rescalePeriodic f ε x) (g ε x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (∫ y, f y ∂cellMeasure d) (∫ x in Ω, g₀ x))) := by
  exact tendsto_integral_rescalePeriodic_inner_strong_along hΩ hΩm hf tendsto_id hg

end KVApproximation.Analysis
