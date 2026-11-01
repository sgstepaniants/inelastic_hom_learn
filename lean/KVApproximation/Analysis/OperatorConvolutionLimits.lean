module

public import KVApproximation.Analysis.CausalConvolution

/-!
# Weak limits of operator convolutions
-/

public section

open MeasureTheory Filter
open scoped Topology Interval

namespace KVApproximation.Analysis

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel limit:
pointwise weak convergence of uniformly bounded continuous operator kernels
passes through causal convolution with an L¹ forcing on a finite horizon.
The target may be any real Banach space; no separability is assumed. -/
theorem tendsto_intervalIntegral_of_weak_operator_tendsto
    {I F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {l : Filter I} [l.IsCountablyGenerated]
    (A : I → ℝ → F →L[ℝ] H) (G : ℝ → F →L[ℝ] H)
    (hA : ∀ i, Continuous (A i)) (hG : Continuous G)
    {C : ℝ} (hbound : ∀ (i : I) (t : ℝ), 0 ≤ t → ‖A i t‖ ≤ C)
    (hweak : ∀ (t : ℝ), 0 ≤ t → ∀ (g : F) (ℓ : H →L[ℝ] ℝ),
      Tendsto (fun i => ℓ (A i t g)) l (𝓝 (ℓ (G t g))))
    (f : ℝ → F) {T : ℝ} (hf : IntervalIntegrable f volume 0 T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (∫ r in (0 : ℝ)..t, A i (t - r) (f r))) l
        (𝓝 (ℓ (∫ r in (0 : ℝ)..t, G (t - r) (f r)))) := by
  intro t ht ℓ
  have hIntA (i : I) :
      IntervalIntegrable (fun r => A i (t - r) (f r)) volume 0 t := by
    simpa only [ContinuousLinearMap.id_apply] using
      intervalIntegrable_posConvolution_integrand
        (ContinuousLinearMap.id ℝ (F →L[ℝ] H)) (A i) f (hA i) hf ht
  have hIntG : IntervalIntegrable (fun r => G (t - r) (f r)) volume 0 t := by
    simpa only [ContinuousLinearMap.id_apply] using
      intervalIntegrable_posConvolution_integrand
        (ContinuousLinearMap.id ℝ (F →L[ℝ] H)) G f hG hf ht
  have hft : IntervalIntegrable f volume 0 t := hf.mono_set <| by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le (ht.1.trans ht.2)]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have hscalar :
      Tendsto (fun i => ∫ r in (0 : ℝ)..t, ℓ (A i (t - r) (f r))) l
        (𝓝 (∫ r in (0 : ℝ)..t, ℓ (G (t - r) (f r)))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun r => ‖ℓ‖ * (C * ‖f r‖))
    · exact Eventually.of_forall fun i =>
        (ℓ.integrable_comp (hIntA i).def').aestronglyMeasurable
    · exact Eventually.of_forall fun i => ae_of_all volume fun r hr => by
        have hr' : r ∈ Set.Ioc (0 : ℝ) t := by
          simpa only [Set.uIoc_of_le ht.1] using hr
        exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((A i (t - r)).le_of_opNorm_le (hbound i (t - r) (sub_nonneg.mpr hr'.2)) (f r))
          (norm_nonneg ℓ))
    · exact (hft.norm.const_mul C).const_mul ‖ℓ‖
    · exact ae_of_all volume fun r hr => by
        have hr' : r ∈ Set.Ioc (0 : ℝ) t := by
          simpa only [Set.uIoc_of_le ht.1] using hr
        exact hweak (t - r) (sub_nonneg.mpr hr'.2) (f r) ℓ
  rw [ℓ.intervalIntegral_comp_comm hIntG] at hscalar
  exact hscalar.congr' (Eventually.of_forall fun i => ℓ.intervalIntegral_comp_comm (hIntA i))

end KVApproximation.Analysis
