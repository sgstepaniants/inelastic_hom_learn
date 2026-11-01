/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive,
Lean 4.35 source closure, for continuous linear operator curves.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integration by parts with a varying bounded operator
-/

public section

open MeasureTheory Set
open scoped Interval

namespace KVApproximation.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Appendix A.3, Duhamel integrability: a continuous operator curve
applied to an integrable vector field remains integrable. -/
theorem intervalIntegrable_continuous_clm_apply {a b : ℝ}
    {Φ : ℝ → E →L[ℝ] F} {f : ℝ → E}
    (hΦ : ContinuousOn Φ (Set.uIcc a b)) (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => Φ t (f t)) volume a b := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hΦ
  rw [intervalIntegrable_iff] at hf ⊢
  have hmΦ : AEStronglyMeasurable Φ (volume.restrict (uIoc a b)) :=
    (hΦ.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  refine (hf.norm.const_mul C).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hmΦ.prodMk hf.aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  exact ((Φ t).le_opNorm (f t)).trans
    (mul_le_mul_of_nonneg_right (hC t (uIoc_subset_uIcc ht)) (norm_nonneg _))

/-- Appendix A.3 (`eq:eta_sol`), integration by parts: a continuously
differentiable operator pairs with the primitive of an integrable field. -/
theorem integral_deriv_clm_primitive_eq_sub_of_le [CompleteSpace E] [CompleteSpace F]
    {a b : ℝ} {Φ : ℝ → E →L[ℝ] F} {f : ℝ → E} (hab : a ≤ b)
    (hΦ : ContDiff ℝ 1 Φ) (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, (deriv Φ t) (∫ s in a..t, f s)) =
      Φ b (∫ s in a..b, f s) - ∫ t in a..b, Φ t (f t) := by
  have hΦd : Continuous (deriv Φ) := hΦ.continuous_deriv le_rfl
  let G : ℝ → ℝ → F := fun t s => (deriv Φ t) ((Iio t).indicator f s)
  have hGi : IntegrableOn (Function.uncurry G) (Ι a b ×ˢ Ι a b) := by
    rw [uIoc_of_le hab]
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      hΦd.continuousOn
    have hfi : Integrable f (volume.restrict (Ioc a b)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine Integrable.mono' ((integrable_const C).mul_prod hfi.norm) ?_ ?_
    · have heq : Function.uncurry G = fun p : ℝ × ℝ =>
          (deriv Φ p.1) ({p : ℝ × ℝ | p.2 < p.1}.indicator (fun p => f p.2) p) := by
        ext ⟨t, s⟩
        simp [G, indicator]
      have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2)
          ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
        hfi.aestronglyMeasurable.comp_snd
      rw [heq]
      exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        ((hΦd.comp continuous_fst).aestronglyMeasurable.prodMk
          (hm.indicator (measurableSet_lt measurable_snd measurable_fst)))
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      have hCp := hC p.1 (Ioc_subset_Icc_self hp.1)
      exact ((deriv Φ p.1).le_opNorm _).trans
        (mul_le_mul hCp (norm_indicator_le_norm_self _ _) (norm_nonneg _)
          ((norm_nonneg _).trans hCp))
  have hleft : EqOn (fun t => ∫ s in a..b, G t s)
      (fun t => (deriv Φ t) (∫ s in a..t, f s)) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hset : Ioc a b ∩ Iio t = Ioo a t := by
      ext s
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by linarith [ht.2]⟩, h.2⟩⟩
    have hind : IntervalIntegrable ((Iio t).indicator f) volume a b :=
      ⟨hf.1.indicator measurableSet_Iio, hf.2.indicator measurableSet_Iio⟩
    change (∫ s in a..b, (deriv Φ t) ((Iio t).indicator f s)) =
      (deriv Φ t) (∫ s in a..t, f s)
    rw [(deriv Φ t).intervalIntegral_comp_comm hind]
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le ht.1,
      setIntegral_indicator measurableSet_Iio, hset, integral_Ioc_eq_integral_Ioo]
  have hright : EqOn (fun s => ∫ t in a..b, G t s)
      (fun s => Φ b (f s) - Φ s (f s)) (uIcc a b) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hGs : ∀ t, G t s = ((Ioi s).indicator (deriv Φ) t) (f s) := by
      intro t
      by_cases hst : s < t <;> simp [G, indicator, hst]
    have hind : IntervalIntegrable ((Ioi s).indicator (deriv Φ)) volume a b :=
      ⟨(hΦd.intervalIntegrable a b).1.indicator measurableSet_Ioi,
        (hΦd.intervalIntegrable a b).2.indicator measurableSet_Ioi⟩
    calc
      (∫ t in a..b, G t s) = (∫ t in a..b, (Ioi s).indicator (deriv Φ) t) (f s) := by
        simp_rw [hGs]
        exact (ContinuousLinearMap.intervalIntegral_apply hind (f s)).symm
      _ = (∫ t in s..b, deriv Φ t) (f s) := by
        rw [intervalIntegral.integral_of_le hab, setIntegral_indicator measurableSet_Ioi,
          Ioc_inter_Ioi, sup_eq_right.2 hs.1, ← intervalIntegral.integral_of_le hs.2]
      _ = Φ b (f s) - Φ s (f s) := by
        rw [intervalIntegral.integral_deriv_eq_sub
          (fun x _ => (hΦ.differentiable one_ne_zero) x) (hΦd.intervalIntegrable _ _)]
        rfl
  rw [← intervalIntegral.integral_congr hleft, intervalIntegral_intervalIntegral_swap hGi,
    intervalIntegral.integral_congr hright,
    intervalIntegral.integral_sub
      (intervalIntegrable_continuous_clm_apply continuousOn_const hf)
      (intervalIntegrable_continuous_clm_apply hΦ.continuous.continuousOn hf),
    (Φ b).intervalIntegral_comp_comm hf]

end KVApproximation.Analysis
