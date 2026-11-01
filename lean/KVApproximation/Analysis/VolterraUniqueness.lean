module

public import KVApproximation.Analysis.CausalConvolution
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Uniqueness for an integrated memory equation

A viscous norm bound reduces the vector equation to a scalar Gronwall
inequality for the integral of the trajectory's norm.
-/

public section

open MeasureTheory Set
open scoped Interval

namespace KVApproximation.Analysis

variable {H F G : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Theorem 3.1, finite-time uniqueness: the integrated homogeneous
memory equation has only the zero continuous trajectory when the viscous
operator controls its norm. No equation is required beyond the finite horizon. -/
theorem eqOn_zero_of_integrated_memory_eq_zero {T : ℝ} (hT : 0 ≤ T)
    (q : ℝ → H) (hq : ContinuousOn q (Icc (0 : ℝ) T))
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (c : ℝ) (hc : 0 ≤ c)
    (hV : ∀ x : H, ‖x‖ ≤ c * ‖V x‖)
    (hbalance : ∀ t ∈ Icc (0 : ℝ) T,
      V (q t) + E (∫ r in (0 : ℝ)..t, q r) +
        posConvolution K q L volume t = 0) :
    EqOn q (fun _ => 0) (Icc (0 : ℝ) T) := by
  have hqi : IntervalIntegrable q volume 0 T := hq.intervalIntegrable_of_Icc hT
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) T) hK.continuousOn
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖q t‖ ≤ (c * (‖E‖ + ‖L‖ * M)) * (∫ r in (0 : ℝ)..t, ‖q r‖) := by
    have hs : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) T := by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2
    have hqt := hqi.mono_set hs
    have hkt := intervalIntegrable_posConvolution_integrand L K q hK hqi ht
    have hmemory : ‖posConvolution K q L volume t‖ ≤
        (‖L‖ * M) * (∫ r in (0 : ℝ)..t, ‖q r‖) := by
      rw [posConvolution_eq_integral_sub L K q ht.1]
      calc
        _ ≤ ∫ r in (0 : ℝ)..t, ‖L (K (t - r)) (q r)‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht.1
        _ ≤ ∫ r in (0 : ℝ)..t, (‖L‖ * M) * ‖q r‖ := by
          apply intervalIntegral.integral_mono_on ht.1 hkt.norm (hqt.norm.const_mul (‖L‖ * M))
          intro r hr
          have htr : t - r ∈ Icc (0 : ℝ) T := by
            constructor <;> linarith [ht.1, ht.2, hr.1, hr.2]
          exact (L.le_opNorm₂ _ _).trans <|
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hM _ htr) (norm_nonneg L)) (norm_nonneg (q r))
        _ = _ := intervalIntegral.integral_const_mul _ _
    have helastic : ‖E (∫ r in (0 : ℝ)..t, q r)‖ ≤
        ‖E‖ * (∫ r in (0 : ℝ)..t, ‖q r‖) :=
      (E.le_opNorm _).trans <| mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm ht.1) (norm_nonneg E)
    have heq : V (q t) = -(E (∫ r in (0 : ℝ)..t, q r) +
        posConvolution K q L volume t) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [← add_assoc] using hbalance t ht
    calc
      ‖q t‖ ≤ c * ‖V (q t)‖ := hV _
      _ = c * ‖E (∫ r in (0 : ℝ)..t, q r) + posConvolution K q L volume t‖ := by
        rw [heq, norm_neg]
      _ ≤ c * (‖E (∫ r in (0 : ℝ)..t, q r)‖ + ‖posConvolution K q L volume t‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hc
      _ ≤ c * (‖E‖ * (∫ r in (0 : ℝ)..t, ‖q r‖) +
          (‖L‖ * M) * (∫ r in (0 : ℝ)..t, ‖q r‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add helastic hmemory) hc
      _ = _ := by ring
  let p : ℝ → ℝ := fun t => ‖q (projIcc 0 T hT t)‖
  have hp : Continuous p :=
    (hq.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => (projIcc 0 T hT t).property)).norm
  have hp_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : p t = ‖q t‖ := by
    simp only [p, projIcc_of_mem hT ht]
  let m : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, p r
  have hm_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      m t = ∫ r in (0 : ℝ)..t, ‖q r‖ := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    exact hp_eq r ⟨hr.1, hr.2.trans ht.2⟩
  have hm_nonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ m t := by
    rw [hm_eq t ht]
    exact intervalIntegral.integral_nonneg ht.1 (fun r _ => norm_nonneg (q r))
  have hm_deriv (t : ℝ) : HasDerivAt m (p t) t :=
    intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable _ _)
      hp.aestronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt
  have hm_cont : Continuous m := continuous_iff_continuousAt.mpr fun t => (hm_deriv t).continuousAt
  have hm_zero : ∀ t ∈ Icc (0 : ℝ) T, m t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (K := c * (‖E‖ + ‖L‖ * M)) hm_cont.continuousOn
      (fun t _ => (hm_deriv t).hasDerivWithinAt) (by simp [m])
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    rw [Real.norm_of_nonneg (show 0 ≤ p t from norm_nonneg _), hp_eq t ht',
      Real.norm_of_nonneg (hm_nonneg t ht'), hm_eq t ht']
    exact hbound t ht'
  intro t ht
  apply norm_le_zero_iff.mp
  calc
    ‖q t‖ ≤ (c * (‖E‖ + ‖L‖ * M)) * (∫ r in (0 : ℝ)..t, ‖q r‖) := hbound t ht
    _ = 0 := by rw [← hm_eq t ht, hm_zero t ht, mul_zero]

/-- Theorem 3.1, Green-balance uniqueness: continuous trajectories
with the same integrated memory balance coincide on the finite horizon.
The right-hand side may vary arbitrarily with time. -/
theorem eqOn_of_integrated_memory_eq {T : ℝ} (hT : 0 ≤ T)
    (u v : ℝ → H) (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hv : ContinuousOn v (Icc (0 : ℝ) T))
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (c : ℝ) (hc : 0 ≤ c)
    (hV : ∀ x : H, ‖x‖ ≤ c * ‖V x‖)
    (hbalance : ∀ t ∈ Icc (0 : ℝ) T,
      V (u t) + E (∫ r in (0 : ℝ)..t, u r) + posConvolution K u L volume t =
        V (v t) + E (∫ r in (0 : ℝ)..t, v r) + posConvolution K v L volume t) :
    EqOn u v (Icc (0 : ℝ) T) := by
  have hiu : IntervalIntegrable u volume 0 T := hu.intervalIntegrable_of_Icc hT
  have hiv : IntervalIntegrable v volume 0 T := hv.intervalIntegrable_of_Icc hT
  let q : ℝ → H := fun t => u t - v t
  have hq : ContinuousOn q (Icc (0 : ℝ) T) := hu.sub hv
  have hzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      V (q t) + E (∫ r in (0 : ℝ)..t, q r) + posConvolution K q L volume t = 0 := by
    have hs : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) T := by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2
    have hprimitive : (∫ r in (0 : ℝ)..t, q r) =
        (∫ r in (0 : ℝ)..t, u r) - ∫ r in (0 : ℝ)..t, v r :=
      intervalIntegral.integral_sub (hiu.mono_set hs) (hiv.mono_set hs)
    have hmemory : posConvolution K q L volume t =
        posConvolution K u L volume t - posConvolution K v L volume t := by
      rw [posConvolution_eq_integral_sub L K q ht.1,
        posConvolution_eq_integral_sub L K u ht.1,
        posConvolution_eq_integral_sub L K v ht.1]
      simp only [q, map_sub]
      exact intervalIntegral.integral_sub
        (intervalIntegrable_posConvolution_integrand L K u hK hiu ht)
        (intervalIntegrable_posConvolution_integrand L K v hK hiv ht)
    rw [show V (q t) = V (u t) - V (v t) from V.map_sub _ _,
      hprimitive, E.map_sub, hmemory]
    calc
      _ = (V (u t) + E (∫ r in (0 : ℝ)..t, u r) + posConvolution K u L volume t) -
          (V (v t) + E (∫ r in (0 : ℝ)..t, v r) + posConvolution K v L volume t) := by abel
      _ = 0 := sub_eq_zero.mpr (hbalance t ht)
  have heq := eqOn_zero_of_integrated_memory_eq_zero hT q hq V E L K hK c hc hV hzero
  intro t ht
  exact sub_eq_zero.mp (heq ht)


end KVApproximation.Analysis
