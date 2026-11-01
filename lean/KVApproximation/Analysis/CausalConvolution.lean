module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-time causal convolution

Continuous kernels act on integrable velocities. The resulting memory term
is continuous, and finite-time integration commutes with the convolution.
-/

public section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace KVApproximation.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Theorem 3.1, time-domain recovery: the causal convolution has
the memory-equation orientation at every nonnegative time, including zero. -/
theorem posConvolution_eq_integral_sub
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {t : ℝ} (ht : 0 ≤ t) :
    posConvolution K f L volume t = ∫ r in (0 : ℝ)..t, L (K (t - r)) (f r) := by
  by_cases ht' : 0 < t
  · rw [posConvolution, indicator_of_mem (s := Ioi (0 : ℝ)) ht']
    simpa only [sub_self, sub_zero, sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
        (fun r => L (K r) (f (t - r))) t).symm
  · have hzero : t = 0 := le_antisymm (not_lt.mp ht') ht
    subst t
    simp [posConvolution]

/-- Theorem 3.1, finite-time Fubini: the lower-triangle indicator
cuts a fixed interval down to its moving endpoint. -/
private theorem integral_lower_indicator (g : ℝ → G) {T t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ r in (0 : ℝ)..T, (Iio t).indicator g r) = ∫ r in (0 : ℝ)..t, g r := by
  have hset : Ioc (0 : ℝ) T ∩ Iio t = Ioo 0 t := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, h.2.le.trans ht.2⟩, h.2⟩⟩
  rw [intervalIntegral.integral_of_le (ht.1.trans ht.2),
    intervalIntegral.integral_of_le ht.1, setIntegral_indicator measurableSet_Iio,
    hset, integral_Ioc_eq_integral_Ioo]

/-- Theorem 3.1, memory integrability: a continuous kernel paired
with an integrable velocity is integrable at every time in the closed horizon. -/
theorem intervalIntegrable_posConvolution_integrand
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {T : ℝ} (hK : Continuous K) (hf : IntervalIntegrable f volume 0 T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun r => L (K (t - r)) (f r)) volume 0 t := by
  have hft : IntervalIntegrable f volume 0 t := hf.mono_set <| by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2
  have hKt : Continuous (fun r => K (t - r)) := hK.comp (continuous_const.sub continuous_id)
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (s := uIcc (0 : ℝ) t) hKt.continuousOn
  rw [intervalIntegrable_iff] at hft ⊢
  refine (hft.norm.const_mul (‖L‖ * C)).mono'
    (L.aestronglyMeasurable_comp₂ hKt.aestronglyMeasurable hft.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  exact (L.le_opNorm₂ _ _).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hC r (uIoc_subset_uIcc hr)) (norm_nonneg L))
      (norm_nonneg (f r)))

/-- Theorem 3.1, continuous memory term: only integrability of the
velocity is needed for continuity of its convolution with a continuous kernel. -/
theorem continuousOn_posConvolution
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {T : ℝ} (hK : Continuous K) (hf : IntervalIntegrable f volume 0 T) :
    ContinuousOn (posConvolution K f L volume) (Icc (0 : ℝ) T) := by
  let J : ℝ → ℝ → G := fun t r => (Iio t).indicator (fun r => L (K (t - r)) (f r)) r
  have hEq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (∫ r in (0 : ℝ)..T, J t r) = posConvolution K f L volume t := by
    rw [posConvolution_eq_integral_sub L K f ht.1]
    exact integral_lower_indicator _ ht
  suffices hcont : ContinuousOn (fun t => ∫ r in (0 : ℝ)..T, J t r) (Icc (0 : ℝ) T) by
    exact hcont.congr fun t ht => (hEq t ht).symm
  intro t₀ ht₀
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-T) T) hK.continuousOn
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun r => (‖L‖ * C) * ‖f r‖) ?_ ?_ (hf.norm.const_mul (‖L‖ * C)) ?_
  · exact Eventually.of_forall fun t =>
      (L.aestronglyMeasurable_comp₂
        (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        hf.def'.aestronglyMeasurable).indicator measurableSet_Iio
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact Eventually.of_forall fun r hr => by
      have hr' : r ∈ Icc (0 : ℝ) T := by
        simpa only [uIcc_of_le hT] using uIoc_subset_uIcc hr
      have hsub : t - r ∈ Icc (-T) T := by constructor <;> linarith [ht.1, ht.2, hr'.1, hr'.2]
      exact (norm_indicator_le_norm_self _ _).trans <|
        (L.le_opNorm₂ _ _).trans <|
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hC _ hsub) (norm_nonneg L)) (norm_nonneg (f r))
  · have hne : ∀ᵐ r : ℝ ∂volume, r ≠ t₀ := by
      exact compl_mem_ae_iff.mpr (measure_singleton t₀)
    filter_upwards [hne] with r hr _
    rcases lt_or_gt_of_ne hr with hlt | hgt
    · have hc : Continuous (fun t => L (K (t - r)) (f r)) :=
        (L.continuous.comp (hK.comp (continuous_id.sub continuous_const))).clm_apply continuous_const
      apply hc.continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlt)] with t ht
        exact indicator_of_mem (s := Iio t) ht (fun r => L (K (t - r)) (f r))
      · exact indicator_of_mem (s := Iio t₀) hlt (fun r => L (K (t₀ - r)) (f r))
    · apply (continuousWithinAt_const (b := (0 : G))).congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hgt)] with t ht
        exact indicator_of_notMem (s := Iio t) (not_lt.mpr ht.le)
          (fun r => L (K (t - r)) (f r))
      · exact indicator_of_notMem (s := Iio t₀) (not_lt.mpr hgt.le)
          (fun r => L (K (t₀ - r)) (f r))

/-- Theorem 3.1, finite-time Fubini: a continuous kernel on a compact
rectangle and one integrable factor give a genuine product-space integral. -/
theorem integrable_rectangle_bilinear
    (L : E →L[ℝ] F →L[ℝ] G) (Φ : ℝ × ℝ → E) (f : ℝ → F)
    {T : ℝ} (hΦ : Continuous Φ) (hf : IntervalIntegrable f volume 0 T) :
    IntegrableOn (fun p : ℝ × ℝ => L (Φ p) (f p.2))
      (uIoc (0 : ℝ) T ×ˢ uIoc (0 : ℝ) T) := by
  let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) T)) :=
    Real.isFiniteMeasure_restrict_Ioc _ _
  have hc : IsCompact (uIcc (0 : ℝ) T ×ˢ uIcc (0 : ℝ) T) :=
    isCompact_uIcc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hΦ.continuousOn
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine Integrable.mono' ((integrable_const (‖L‖ * C)).mul_prod hf.def'.norm)
    (L.aestronglyMeasurable_comp₂ hΦ.aestronglyMeasurable
      hf.def'.aestronglyMeasurable.comp_snd) ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_uIoc)] with p hp
  exact (L.le_opNorm₂ _ _).trans <|
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (hC p ⟨uIoc_subset_uIcc hp.1, uIoc_subset_uIcc hp.2⟩) (norm_nonneg L))
      (norm_nonneg (f p.2))

/-- Theorem 3.1, integrated weak equation: Fubini on a finite triangle
exchanges the time variable and the earlier integration time. -/
theorem integral_triangle_swap [CompleteSpace G]
    (Φ : ℝ → ℝ → G) {T : ℝ} (hT : 0 ≤ T)
    (hΦ : IntegrableOn (Function.uncurry Φ) (uIoc (0 : ℝ) T ×ˢ uIoc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, ∫ r in (0 : ℝ)..t, Φ t r) =
      ∫ r in (0 : ℝ)..T, ∫ t in r..T, Φ t r := by
  let J : ℝ → ℝ → G := fun t r => (Iio t).indicator (Φ t) r
  have hJ : IntegrableOn (Function.uncurry J)
      (uIoc (0 : ℝ) T ×ˢ uIoc (0 : ℝ) T) := by
    have heq : Function.uncurry J =
        {p : ℝ × ℝ | p.2 < p.1}.indicator (Function.uncurry Φ) := by
      rfl
    rw [heq]
    exact hΦ.indicator (measurableSet_lt measurable_snd measurable_fst)
  have hleft : EqOn (fun t => ∫ r in (0 : ℝ)..T, J t r)
      (fun t => ∫ r in (0 : ℝ)..t, Φ t r) (uIcc (0 : ℝ) T) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact integral_lower_indicator _ ht
  have hright : EqOn (fun r => ∫ t in (0 : ℝ)..T, J t r)
      (fun r => ∫ t in r..T, Φ t r) (uIcc (0 : ℝ) T) := by
    intro r hr
    rw [uIcc_of_le hT] at hr
    have heq : (fun t => J t r) = (Ioi r).indicator (fun t => Φ t r) := by
      funext t
      by_cases hrt : r < t <;> simp [J, indicator, hrt]
    change (∫ t in (0 : ℝ)..T, J t r) = ∫ t in r..T, Φ t r
    rw [heq, intervalIntegral.integral_of_le hT,
      setIntegral_indicator measurableSet_Ioi, Ioc_inter_Ioi,
      sup_eq_right.mpr hr.1, ← intervalIntegral.integral_of_le hr.2]
  calc
    _ = ∫ t in (0 : ℝ)..T, ∫ r in (0 : ℝ)..T, J t r :=
      (intervalIntegral.integral_congr hleft).symm
    _ = ∫ r in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, J t r :=
      intervalIntegral_intervalIntegral_swap hJ
    _ = _ := intervalIntegral.integral_congr hright

/-- Theorem 3.1, Duhamel integration: finite-triangle Fubini integrates
the kernel before the forcing, without requiring completeness of the input. -/
theorem integral_posConvolution_eq_integral_kernel [CompleteSpace G]
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {T : ℝ} (hT : 0 ≤ T) (hK : Continuous K)
    (hf : IntervalIntegrable f volume 0 T) :
    (∫ t in (0 : ℝ)..T, posConvolution K f L volume t) =
      ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..(T - r), L (K s) (f r) := by
  calc
    _ = ∫ t in (0 : ℝ)..T, ∫ r in (0 : ℝ)..t, L (K (t - r)) (f r) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT] at ht
      exact posConvolution_eq_integral_sub L K f ht.1
    _ = ∫ r in (0 : ℝ)..T, ∫ t in r..T, L (K (t - r)) (f r) :=
      integral_triangle_swap _ hT
        (integrable_rectangle_bilinear L (fun p => K (p.1 - p.2)) f
          (hK.comp (continuous_fst.sub continuous_snd)) hf)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      simpa only [sub_self] using
        intervalIntegral.integral_comp_sub_right (a := r) (b := T)
          (fun s => L (K s) (f r)) r

/-- Theorem 3.1, integrated weak equation: finite-time Fubini moves
the primitive through the memory convolution without differentiating the kernel. -/
theorem integral_posConvolution_eq_posConvolution_primitive
    [CompleteSpace F] [CompleteSpace G]
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {T : ℝ} (hT : 0 ≤ T) (hK : Continuous K)
    (hf : IntervalIntegrable f volume 0 T) :
    (∫ t in (0 : ℝ)..T, posConvolution K f L volume t) =
      posConvolution K (fun t => ∫ r in (0 : ℝ)..t, f r) L volume T := by
  have hfirst := integral_posConvolution_eq_integral_kernel L K f hT hK hf
  have hsecond : posConvolution K (fun t => ∫ r in (0 : ℝ)..t, f r) L volume T =
      ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..(T - r), L (K s) (f r) := by
    rw [posConvolution_eq_integral_sub L K _ hT]
    calc
      _ = ∫ t in (0 : ℝ)..T, ∫ r in (0 : ℝ)..t, L (K (T - t)) (f r) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact ((L (K (T - t))).intervalIntegral_comp_comm
          (hf.mono_set (uIcc_subset_uIcc left_mem_uIcc ht))).symm
      _ = ∫ r in (0 : ℝ)..T, ∫ t in r..T, L (K (T - t)) (f r) :=
        integral_triangle_swap _ hT
          (integrable_rectangle_bilinear L (fun p => K (T - p.1)) f
            (hK.comp (continuous_const.sub continuous_fst)) hf)
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro r hr
        simpa only [sub_self] using
          intervalIntegral.integral_comp_sub_left (a := r) (b := T)
            (fun s => L (K s) (f r)) T
  exact hfirst.trans hsecond.symm

end KVApproximation.Analysis
