module

public import KVApproximation.Dynamics.DampedResponse
public import KVApproximation.Analysis.PrimitiveIntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.FieldSimp

/-!
# Bounds and evolution of exponential responses
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis

namespace KVApproximation.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Proposition B.10: separate the integrating factor from the primitive. -/
private theorem dampedResponse_factor (rate : ℝ) (v : ℝ → E) (t : ℝ) :
    dampedResponse rate v t = Real.exp (-rate * t) •
      ∫ s in (0 : ℝ)..t, Real.exp (rate * s) • v s := by
  rw [dampedResponse, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [smul_smul, ← Real.exp_add]
  congr 2
  ring

/-- Lemma B.11: the scalar exponential majorant has an exact primitive. -/
private theorem integral_damping_kernel {rate t : ℝ} (hrate : 0 < rate) :
    (∫ s in (0 : ℝ)..t, Real.exp (-rate * (t - s))) =
      (1 - Real.exp (-rate * t)) / rate := by
  have hd (s : ℝ) : HasDerivAt (fun s => Real.exp (-rate * (t - s)) / rate)
      (Real.exp (-rate * (t - s))) s := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, neg_mul_neg, mul_one,
      mul_div_cancel_right₀ _ hrate.ne'] using
      ((((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-rate)).exp.div_const rate)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (Continuous.intervalIntegrable (by fun_prop) 0 t)]
  simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
  ring

/-- Lemma B.11, convolution estimate: the finite-time exponential factor
is retained in the bound for a bounded forcing. -/
theorem norm_dampedResponse_le (v : ℝ → E) {rate M t : ℝ}
    (hrate : 0 < rate) (ht : 0 ≤ t)
    (hbound : ∀ᵐ s ∂timeMeasure, ‖v s‖ ≤ M) :
    ‖dampedResponse rate v t‖ ≤ M * (1 - Real.exp (-rate * t)) / rate := by
  have hb : ∀ᵐ s ∂volume, s ∈ Set.Ioc 0 t →
      ‖Real.exp (-rate * (t - s)) • v s‖ ≤ Real.exp (-rate * (t - s)) * M := by
    filter_upwards [ae_imp_of_ae_restrict hbound] with s hs hst
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hs hst.1.le) (Real.exp_pos _).le
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, Real.exp (-rate * (t - s)) * M :=
      intervalIntegral.norm_integral_le_of_norm_le ht hb
        (Continuous.intervalIntegrable (by fun_prop) 0 t)
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, integral_damping_kernel hrate]
      ring

/-- Proposition B.10, Duhamel formula: locally integrable forcing gives
a continuous response on the nonnegative time axis. -/
theorem continuousOn_dampedResponse (rate : ℝ) (v : ℝ → E)
    (hv : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable v volume 0 t) :
    ContinuousOn (dampedResponse rate v) (Set.Ici 0) := by
  intro t ht
  have ht' : 0 ≤ t := ht
  have hT : 0 ≤ t + 1 := by linarith
  have hfi : IntervalIntegrable (fun s => Real.exp (rate * s) • v s) volume 0 (t + 1) :=
    (hv (t + 1) hT).continuousOn_smul (by fun_prop)
  have hp := intervalIntegral.continuousOn_primitive_interval' hfi (Set.left_mem_uIcc)
  rw [Set.uIcc_of_le hT] at hp
  have hq : ContinuousOn (dampedResponse rate v) (Set.Icc 0 (t + 1)) := by
    have hc := (show ContinuousOn (fun s : ℝ => Real.exp (-rate * s))
      (Set.Icc 0 (t + 1)) by fun_prop).smul hp
    exact hc.congr (fun s _ => dampedResponse_factor rate v s)
  apply (hq t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith : t < t + 1)))

/-- Proposition B.10 (`eq:q_i_ode`, `eq:q_i_duhamel`): the exponential
convolution satisfies the integral form of the linear evolution equation. -/
theorem dampedResponse_integral_eq (rate : ℝ) (v : ℝ → E)
    (hv : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable v volume 0 t)
    {t : ℝ} (ht : 0 ≤ t) :
    dampedResponse rate v t =
      ∫ s in (0 : ℝ)..t, v s - rate • dampedResponse rate v s := by
  let φ : ℝ → ℝ := fun s => Real.exp (-rate * s)
  let f : ℝ → E := fun s => Real.exp (rate * s) • v s
  have hφ : ContDiff ℝ 1 φ := by dsimp only [φ]; fun_prop
  have hd (s : ℝ) : deriv φ s = -rate * φ s := by
    simpa only [φ, id_eq, mul_one, mul_comm] using
      (((hasDerivAt_id s).const_mul (-rate)).exp).deriv
  have hfi : IntervalIntegrable f volume 0 t :=
    (hv t ht).continuousOn_smul (by fun_prop)
  have hpair (s : ℝ) : φ s • f s = v s := by
    dsimp only [φ, f]
    rw [smul_smul, ← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero, one_smul]
  have hleft (s : ℝ) : deriv φ s • (∫ r in (0 : ℝ)..s, f r) =
      -rate • dampedResponse rate v s := by
    rw [hd, mul_smul, dampedResponse_factor]
  have hparts := integral_deriv_smul_primitive_eq_sub_of_le ht hφ hfi
  simp_rw [hleft, hpair] at hparts
  rw [show φ t • (∫ s in (0 : ℝ)..t, f s) = dampedResponse rate v t from
    (dampedResponse_factor rate v t).symm, intervalIntegral.integral_smul] at hparts
  have hqi : IntervalIntegrable (dampedResponse rate v) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht]
    exact (continuousOn_dampedResponse rate v hv).mono (fun _ hs => hs.1)
  have hri : IntervalIntegrable (fun s => rate • dampedResponse rate v s) volume 0 t :=
    hqi.smul rate
  rw [intervalIntegral.integral_sub (hv t ht) hri,
    intervalIntegral.integral_smul]
  calc
    _ = (dampedResponse rate v t - ∫ s in (0 : ℝ)..t, v s) +
        ∫ s in (0 : ℝ)..t, v s := by abel
    _ = (-rate) • (∫ s in (0 : ℝ)..t, dampedResponse rate v s) +
        ∫ s in (0 : ℝ)..t, v s := by rw [hparts]
    _ = _ := by rw [neg_smul]; abel

/-- Proposition B.10: positive damping and essentially bounded forcing
give a bounded Sobolev trajectory with the prescribed convolution values. -/
theorem dampedResponse_trajectory {rate : ℝ} (hrate : 0 < rate)
    (v : ℝ → E) (hv : MemLp v ⊤ timeMeasure) :
    ∃ q : BoundedTrajectory E,
      (∀ t : ℝ, 0 ≤ t → q.value t = dampedResponse rate v t) ∧
      q.value 0 = 0 ∧
      ∀ᵐ t ∂timeMeasure, q.velocity t = v t - rate • q.value t := by
  have hlocal (t : ℝ) (ht : 0 ≤ t) : IntervalIntegrable v volume 0 t := by
    let : IsFiniteMeasure (volume.restrict (Set.uIoc 0 t)) :=
      ⟨by simp [Set.uIoc, Real.volume_Ioc]⟩
    rw [intervalIntegrable_iff]
    apply MemLp.integrable le_top
    exact MemLp.mono_measure
      (Measure.restrict_mono_set volume (fun x hx => (le_min le_rfl ht).trans hx.1.le)) hv
  let M := (eLpNorm v ⊤ timeMeasure).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hbound : ∀ᵐ s ∂timeMeasure, ‖v s‖ ≤ M := ae_le_lpNorm_exponent_top hv
  have hq : MemLp (dampedResponse rate v) ⊤ timeMeasure := by
    apply memLp_top_of_bound
      ((continuousOn_dampedResponse rate v hlocal).aestronglyMeasurable measurableSet_Ici)
      (M / rate)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    calc
      _ ≤ M * (1 - Real.exp (-rate * t)) / rate := norm_dampedResponse_le v hrate ht hbound
      _ ≤ M / rate := div_le_div_of_nonneg_right
        (by nlinarith [Real.exp_pos (-rate * t)]) hrate.le
  have hzero : dampedResponse rate v 0 = 0 := by simp [dampedResponse]
  refine ⟨{
    value := dampedResponse rate v
    velocity := fun t => v t - rate • dampedResponse rate v t
    value_memLp := hq
    velocity_memLp := hv.sub (hq.const_smul rate)
    integral_eq := ?_
  }, fun _ _ => rfl, hzero, Filter.Eventually.of_forall (fun _ => rfl)⟩
  intro t ht
  simpa only [hzero, zero_add] using dampedResponse_integral_eq rate v hlocal ht

end KVApproximation.Dynamics
