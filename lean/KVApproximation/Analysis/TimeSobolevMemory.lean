module

public import KVApproximation.Analysis.TimeSobolevProperties
public import KVApproximation.Analysis.CausalConvolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Integrated Sobolev equations with memory

The continuous trace and the primitive of its weak derivative identify the
integrated equation. Differentiating the vector-valued residual recovers one
almost-everywhere equation before applying any test functional.
-/

public section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace KVApproximation.Analysis

variable {H F G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Theorem 3.1, recovery of the weak equation: a vanishing vector-valued
primitive gives one full-measure set on which its integrable derivative vanishes. -/
private theorem ae_eq_zero_iff_integral_eq_zero {T : ℝ} (hT : 0 < T)
    {f : ℝ → G} (hf : IntervalIntegrable f volume 0 T) :
    (∀ᵐ t ∂volume.restrict (Ioo 0 T), f t = 0) ↔
      ∀ t : Icc (0 : ℝ) T, (∫ r in (0 : ℝ)..(t : ℝ), f r) = 0 := by
  constructor
  · intro h t
    have heq : f =ᵐ[volume.restrict (uIoc (0 : ℝ) (t : ℝ))] fun _ => 0 := by
      rw [uIoc_of_le t.property.1, ← restrict_Ioo_eq_restrict_Ioc]
      exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl t.property.2) h
    simpa only [intervalIntegral.integral_zero] using
      intervalIntegral.integral_congr_ae_restrict heq
  · intro h
    filter_upwards [ae_restrict_of_ae hf.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioo] with t hd ht
    have hmem : t ∈ uIcc (0 : ℝ) T := by
      simpa only [uIcc_of_le hT.le] using (show t ∈ Icc (0 : ℝ) T from ⟨ht.1.le, ht.2.le⟩)
    have hd' := hd hmem 0 left_mem_uIcc
    have hz : HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, f r) (0 : G) t := by
      apply (hasDerivAt_const t (0 : G)).congr_of_eventuallyEq
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with x hx
      exact h ⟨x, hx⟩
    exact hd'.unique hz

/-- Theorem 3.1, recovery of the weak evolution equation: the
Banach-valued balance almost everywhere is equivalent to its integrated
identity at every closed-interval trace. The exceptional null set is chosen
before applying any continuous linear test functional. -/
theorem TimeH1.memory_equation_iff_integrated {T : ℝ} (hT : 0 < T)
    (u : TimeH1 H T) (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (g : ℝ → G)
    (hg : IntervalIntegrable g volume 0 T) :
    let q : ℝ → H := fun t => TimeH1.trace hT u (Set.projIcc 0 T hT.le t)
    (∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      V (TimeH1.velocity u t) + E (TimeH1.value u t) +
        posConvolution K (TimeH1.velocity u) L volume t = g t) ↔
    ∀ t : Set.Icc (0 : ℝ) T,
      V (q t - TimeH1.initial hT u) + E (∫ r in (0 : ℝ)..(t : ℝ), q r) +
        posConvolution K (fun r => q r - TimeH1.initial hT u) L volume t =
          ∫ r in (0 : ℝ)..(t : ℝ), g r := by
  let q : ℝ → H := fun t => TimeH1.trace hT u (Set.projIcc 0 T hT.le t)
  have hvel : IntervalIntegrable (TimeH1.velocity u) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2
      ((TimeH1.velocity_memLp u).integrable (by norm_num))
  have hval : IntervalIntegrable (TimeH1.value u) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2
      ((TimeH1.value_memLp u).integrable (by norm_num))
  have hV : IntervalIntegrable (fun t => V (TimeH1.velocity u t)) volume 0 T :=
    ⟨V.integrable_comp hvel.1, V.integrable_comp hvel.2⟩
  have hE : IntervalIntegrable (fun t => E (TimeH1.value u t)) volume 0 T :=
    ⟨E.integrable_comp hval.1, E.integrable_comp hval.2⟩
  have hconv : IntervalIntegrable (posConvolution K (TimeH1.velocity u) L volume)
      volume 0 T :=
    (continuousOn_posConvolution L K (TimeH1.velocity u) hK hvel).intervalIntegrable_of_Icc hT.le
  let R : ℝ → G := fun t => V (TimeH1.velocity u t) + E (TimeH1.value u t) +
    posConvolution K (TimeH1.velocity u) L volume t - g t
  have hR : IntervalIntegrable R volume 0 T := ((hV.add hE).add hconv).sub hg
  have hprim (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) :
      (∫ s in (0 : ℝ)..r, TimeH1.velocity u s) = q r - TimeH1.initial hT u := by
    have h := TimeH1.trace_integral hT u ⟨r, hr⟩
    have hq : q r = TimeH1.trace hT u ⟨r, hr⟩ := by
      simp only [q, projIcc_of_mem hT.le hr]
    rw [← hq] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h.symm)
  have hint (t : Icc (0 : ℝ) T) :
      (∫ r in (0 : ℝ)..(t : ℝ), R r) =
        V (q t - TimeH1.initial hT u) + E (∫ r in (0 : ℝ)..(t : ℝ), q r) +
          posConvolution K (fun r => q r - TimeH1.initial hT u) L volume t -
            ∫ r in (0 : ℝ)..(t : ℝ), g r := by
    have hs : uIcc (0 : ℝ) (t : ℝ) ⊆ uIcc (0 : ℝ) T :=
      uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hT.le] using t.property)
    have hvalue : (∫ r in (0 : ℝ)..(t : ℝ), TimeH1.value u r) =
        ∫ r in (0 : ℝ)..(t : ℝ), q r := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le t.property.1, ← restrict_Ioo_eq_restrict_Ioc]
      exact ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo le_rfl t.property.2) (TimeH1.trace_ae hT u)
    have hmemory : (∫ r in (0 : ℝ)..(t : ℝ),
        posConvolution K (TimeH1.velocity u) L volume r) =
        posConvolution K (fun r => q r - TimeH1.initial hT u) L volume t := by
      rw [integral_posConvolution_eq_posConvolution_primitive L K (TimeH1.velocity u)
        t.property.1 hK (hvel.mono_set hs),
        posConvolution_eq_integral_sub L K _ t.property.1,
        posConvolution_eq_integral_sub L K _ t.property.1]
      apply intervalIntegral.integral_congr
      intro r hr
      have hrT : r ∈ Icc (0 : ℝ) T := by
        simpa only [uIcc_of_le hT.le] using hs hr
      exact congrArg (fun z => L (K ((t : ℝ) - r)) z) (hprim r hrT)
    change (∫ r in (0 : ℝ)..(t : ℝ),
      (V (TimeH1.velocity u r) + E (TimeH1.value u r) +
        posConvolution K (TimeH1.velocity u) L volume r) - g r) = _
    rw [intervalIntegral.integral_sub (((hV.add hE).add hconv).mono_set hs) (hg.mono_set hs),
      intervalIntegral.integral_add ((hV.add hE).mono_set hs) (hconv.mono_set hs),
      intervalIntegral.integral_add (hV.mono_set hs) (hE.mono_set hs),
      V.intervalIntegral_comp_comm (hvel.mono_set hs),
      E.intervalIntegral_comp_comm (hval.mono_set hs), hprim t t.property, hvalue, hmemory]
  have hzero := ae_eq_zero_iff_integral_eq_zero hT hR
  constructor
  · intro h t
    have hz : ∀ᵐ r ∂volume.restrict (Ioo 0 T), R r = 0 :=
      h.mono fun r hr => sub_eq_zero.mpr hr
    exact sub_eq_zero.mp ((hint t).symm.trans (hzero.mp hz t))
  · intro h
    have hz := hzero.mpr fun t => (hint t).trans (sub_eq_zero.mpr (h t))
    exact hz.mono fun r hr => sub_eq_zero.mp hr

end KVApproximation.Analysis
