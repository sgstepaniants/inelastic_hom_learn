module

public import KVApproximation.Analysis.CausalConvolution
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Continuity and exponential bounds for half-line convolution
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace KVApproximation.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Theorem 3.1, time-domain recovery: a continuous kernel and local
time integrability give a continuous memory term on the closed half-line. -/
theorem continuousOn_posConvolution_Ici
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    (hK : Continuous K)
    (hf : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable f volume 0 T) :
    ContinuousOn (posConvolution K f L volume) (Set.Ici (0 : ℝ)) := by
  intro t ht
  have hT : 0 ≤ t + 1 := by linarith [show 0 ≤ t from ht]
  have hc := continuousOn_posConvolution L K f hK (hf (t + 1) hT)
    t ⟨ht, by linarith⟩
  apply hc.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (lt_add_one t))] with r hr hr'
  exact ⟨hr, hr'⟩

/-- Theorem 3.1, damped integrated residual: an exponentially
integrable kernel acting on a bounded continuous trajectory gives a uniformly
bounded damped memory term, with the exact bilinear operator-norm factor. -/
theorem norm_exp_smul_posConvolution_le
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    (hK : Continuous K) (hf : ContinuousOn f (Set.Ici (0 : ℝ)))
    {M : ℝ} (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M)
    {a : ℝ} (ha : 0 ≤ a)
    (hKi : IntegrableOn (fun r => Real.exp (-a * r) • K r) (Set.Ioi (0 : ℝ)))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Real.exp (-a * t) • posConvolution K f L volume t‖ ≤
      ‖L‖ * M * (∫ r in Set.Ioi (0 : ℝ), ‖Real.exp (-a * r) • K r‖) := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hbound 0 le_rfl)
  have hconv : posConvolution K f L volume t =
      ∫ r in (0 : ℝ)..t, L (K r) (f (t - r)) := by
    by_cases hpos : 0 < t
    · exact indicator_of_mem hpos _
    · have hz : t = 0 := le_antisymm (not_lt.mp hpos) ht
      subst t
      simp [posConvolution]
  have hfsub : ContinuousOn (fun r => f (t - r)) (Icc (0 : ℝ) t) :=
    hf.comp (continuous_const.sub continuous_id).continuousOn
      (fun r hr => sub_nonneg.mpr hr.2)
  have hi : IntervalIntegrable (fun r => Real.exp (-a * t) • L (K r) (f (t - r)))
      volume 0 t :=
    (((L.continuous.comp hK).continuousOn.clm_apply hfsub).const_smul
      (Real.exp (-a * t))).intervalIntegrable_of_Icc ht
  have hKn : IntegrableOn (fun r => ‖Real.exp (-a * r) • K r‖) (Ioi (0 : ℝ)) :=
    hKi.norm
  have hn : IntervalIntegrable (fun r => ‖Real.exp (-a * r) • K r‖) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
      (hKn.mono_set (fun _ hr => hr.1))
  have hb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) t) :
      ‖Real.exp (-a * t) • L (K r) (f (t - r))‖ ≤
        ‖L‖ * M * ‖Real.exp (-a * r) • K r‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-a * t) * (‖L‖ * ‖K r‖ * M) :=
        mul_le_mul_of_nonneg_left
          ((L.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_left
            (hbound (t - r) (sub_nonneg.mpr hr.2))
            (mul_nonneg (norm_nonneg L) (norm_nonneg (K r))))) (Real.exp_pos _).le
      _ ≤ Real.exp (-a * r) * (‖L‖ * ‖K r‖ * M) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
          nlinarith [mul_nonneg ha (sub_nonneg.mpr hr.2)]))
          (mul_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg (K r))) hM)
      _ = _ := by ring
  calc
    _ = ‖∫ r in (0 : ℝ)..t, Real.exp (-a * t) • L (K r) (f (t - r))‖ := by
      rw [hconv, intervalIntegral.integral_smul]
    _ ≤ ∫ r in (0 : ℝ)..t, ‖Real.exp (-a * t) • L (K r) (f (t - r))‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ r in (0 : ℝ)..t, ‖L‖ * M * ‖Real.exp (-a * r) • K r‖ :=
      intervalIntegral.integral_mono_on ht hi.norm (hn.const_mul (‖L‖ * M)) hb
    _ = ‖L‖ * M * (∫ r in Ioc (0 : ℝ) t, ‖Real.exp (-a * r) • K r‖) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le ht]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hKi.norm (Eventually.of_forall fun r => norm_nonneg _)
        (show Ioc (0 : ℝ) t ⊆ Ioi 0 from fun _ hr => hr.1).eventuallySubset)
      (mul_nonneg (norm_nonneg L) hM)

end KVApproximation.Analysis
