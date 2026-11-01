module

public import KVApproximation.Analysis.CausalConvolution

/-!
# Operator convolution and the forced memory equation
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval

namespace KVApproximation.Analysis

variable {F H Y : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel's memory term:
finite-triangle Fubini exchanges a continuous operator kernel with the
causal integral of an L¹ forcing. -/
theorem integral_operatorConvolution_assoc
    (A : ℝ → H →L[ℝ] Y) (G : ℝ → F →L[ℝ] H) (f : ℝ → F)
    {T : ℝ} (hT : 0 ≤ T) (hA : Continuous A) (hG : Continuous G)
    (hf : IntervalIntegrable f volume 0 T) :
    (∫ s in (0 : ℝ)..T, A (T - s) (∫ r in (0 : ℝ)..s, G (s - r) (f r))) =
      ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..(T - r),
        A (T - r - s) (G s (f r)) := by
  have hΦ : Continuous (fun p : ℝ × ℝ => (A (T - p.1)).comp (G (p.1 - p.2))) :=
    (hA.comp (continuous_const.sub continuous_fst)).clm_comp
      (hG.comp (continuous_fst.sub continuous_snd))
  calc
    _ = ∫ s in (0 : ℝ)..T, ∫ r in (0 : ℝ)..s, A (T - s) (G (s - r) (f r)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hInt : IntervalIntegrable (fun r => G (s - r) (f r)) volume 0 s := by
        simpa only [ContinuousLinearMap.id_apply] using
          intervalIntegrable_posConvolution_integrand
            (ContinuousLinearMap.id ℝ (F →L[ℝ] H)) G f hG hf
            (by simpa only [uIcc_of_le hT] using hs)
      exact ((A (T - s)).intervalIntegral_comp_comm hInt).symm
    _ = ∫ r in (0 : ℝ)..T, ∫ s in r..T, A (T - s) (G (s - r) (f r)) := by
      apply integral_triangle_swap _ hT
      change IntegrableOn (fun p : ℝ × ℝ => A (T - p.1) (G (p.1 - p.2) (f p.2)))
        (uIoc (0 : ℝ) T ×ˢ uIoc (0 : ℝ) T)
      simpa only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] using
        integrable_rectangle_bilinear (ContinuousLinearMap.id ℝ (F →L[ℝ] Y))
          (fun p : ℝ × ℝ => (A (T - p.1)).comp (G (p.1 - p.2))) f hΦ hf
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      calc
        _ = ∫ s in r..T, A (T - r - (s - r)) (G (s - r) (f r)) := by
          apply intervalIntegral.integral_congr
          intro s hs
          dsimp only
          rw [show T - r - (s - r) = T - s by ring]
        _ = _ := by
          simpa only [sub_self] using
            intervalIntegral.integral_comp_sub_right (a := r) (b := T)
              (fun s => A (T - r - s) (G s (f r))) r

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), forced integrated
equation: causal integration of the constant-load Green balance gives
the memory equation for arbitrary L¹ forcing, without differentiating a kernel. -/
theorem duhamel_integrated_memory_balance
    (V E : H →L[ℝ] Y) (K : ℝ → H →L[ℝ] Y)
    (G : ℝ → F →L[ℝ] H) (B : F →L[ℝ] Y)
    (hK : Continuous K) (hG : Continuous G)
    (hbalance : ∀ (t : ℝ), 0 ≤ t → ∀ g : F,
      V (G t g) + E (∫ s in (0 : ℝ)..t, G s g) +
        (∫ s in (0 : ℝ)..t, K (t - s) (G s g)) = B g)
    (f : ℝ → F) {T : ℝ} (hf : IntervalIntegrable f volume 0 T) :
    let q : ℝ → H := fun t => ∫ r in (0 : ℝ)..t, G (t - r) (f r)
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      V (q t) + E (∫ s in (0 : ℝ)..t, q s) +
        (∫ s in (0 : ℝ)..t, K (t - s) (q s)) = ∫ r in (0 : ℝ)..t, B (f r) := by
  dsimp only
  intro t ht
  have hft : IntervalIntegrable f volume 0 t := hf.mono_set <| by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2
  let P : ℝ → F →L[ℝ] H := fun s => ∫ r in (0 : ℝ)..s, G r
  have hP : Continuous P :=
    intervalIntegral.continuous_primitive (fun _ _ => hG.intervalIntegrable _ _) 0
  have hP_apply (s : ℝ) (g : F) : P s g = ∫ r in (0 : ℝ)..s, G r g :=
    ContinuousLinearMap.intervalIntegral_apply (hG.intervalIntegrable _ _) g
  have hIntG : IntervalIntegrable (fun r => G (t - r) (f r)) volume 0 t := by
    simpa only [ContinuousLinearMap.id_apply] using
      intervalIntegrable_posConvolution_integrand
        (ContinuousLinearMap.id ℝ (F →L[ℝ] H)) G f hG hft ⟨ht.1, le_rfl⟩
  have hIntP : IntervalIntegrable (fun r => P (t - r) (f r)) volume 0 t := by
    simpa only [ContinuousLinearMap.id_apply] using
      intervalIntegrable_posConvolution_integrand
        (ContinuousLinearMap.id ℝ (F →L[ℝ] H)) P f hP hft ⟨ht.1, le_rfl⟩
  have hV : IntervalIntegrable (fun r => V (G (t - r) (f r))) volume 0 t := by
    rw [intervalIntegrable_iff]
    exact V.integrable_comp hIntG.def'
  have hE : IntervalIntegrable (fun r => E (P (t - r) (f r))) volume 0 t := by
    rw [intervalIntegrable_iff]
    exact E.integrable_comp hIntP.def'
  have hB : IntervalIntegrable (fun r => B (f r)) volume 0 t := by
    rw [intervalIntegrable_iff]
    exact B.integrable_comp hft.def'
  have hMem : IntervalIntegrable
      (fun r => ∫ s in (0 : ℝ)..(t - r), K (t - r - s) (G s (f r))) volume 0 t := by
    apply (hB.sub (hV.add hE)).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    have hr' : r ∈ Ioc (0 : ℝ) t := by simpa only [uIoc_of_le ht.1] using hr
    have hb := hbalance (t - r) (sub_nonneg.mpr hr'.2) (f r)
    rw [← hP_apply] at hb
    exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hb)).symm
  have hprimitive :
      (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, G (s - r) (f r)) =
        ∫ r in (0 : ℝ)..t, P (t - r) (f r) := by
    calc
      _ = ∫ s in (0 : ℝ)..t,
          posConvolution G f (ContinuousLinearMap.id ℝ (F →L[ℝ] H)) volume s := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hs
        simpa only [ContinuousLinearMap.id_apply] using
          (posConvolution_eq_integral_sub
            (ContinuousLinearMap.id ℝ (F →L[ℝ] H)) G f hs'.1).symm
      _ = ∫ r in (0 : ℝ)..t, ∫ s in (0 : ℝ)..(t - r), G s (f r) :=
        integral_posConvolution_eq_integral_kernel
          (ContinuousLinearMap.id ℝ (F →L[ℝ] H)) G f ht.1 hG hft
      _ = _ := intervalIntegral.integral_congr fun r _ => (hP_apply (t - r) (f r)).symm
  rw [hprimitive, ← V.intervalIntegral_comp_comm hIntG,
    ← E.intervalIntegral_comp_comm hIntP,
    integral_operatorConvolution_assoc K G f ht.1 hK hG hft,
    ← intervalIntegral.integral_add hV hE,
    ← intervalIntegral.integral_add (hV.add hE) hMem]
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hr
  simpa only [hP_apply] using hbalance (t - r) (sub_nonneg.mpr hr'.2) (f r)

end KVApproximation.Analysis
