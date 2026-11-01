module

public import KVApproximation.Analysis.TimeSobolevProperties
public import KVApproximation.Analysis.OperatorPrimitive
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Variation of constants for finite-time H¹ solutions
-/

public section

open MeasureTheory Set
open KVApproximation.Analysis

namespace KVApproximation.Dynamics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.3: integration by parts against the continuous time trace. -/
private theorem timeH1_operator_product_integral {T : ℝ} (hT : 0 < T)
    (u : TimeH1 H T) {Φ : ℝ → H →L[ℝ] H} (hΦ : ContDiff ℝ 1 Φ)
    (t : Icc (0 : ℝ) T) :
    Φ t (TimeH1.trace hT u t) = Φ 0 (TimeH1.initial hT u) +
      ∫ s in (0 : ℝ)..(t : ℝ),
        (deriv Φ s) (TimeH1.trace hT u (projIcc 0 T hT.le s)) +
          Φ s (TimeH1.velocity u s) := by
  have hvelon : IntegrableOn (TimeH1.velocity u) (Ioo 0 T) :=
    (TimeH1.velocity_memLp u).integrable (by norm_num)
  have hvel : IntervalIntegrable (TimeH1.velocity u) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le t.property.1).2
      (hvelon.mono_set (Ioo_subset_Ioo le_rfl t.property.2))
  let p : ℝ → H := fun s => ∫ r in (0 : ℝ)..s, TimeH1.velocity u r
  have hp : ContinuousOn p (uIcc 0 (t : ℝ)) :=
    intervalIntegral.continuousOn_primitive_interval' hvel left_mem_uIcc
  have hΦd : Continuous (deriv Φ) := hΦ.continuous_deriv le_rfl
  have hiC : IntervalIntegrable
      (fun s => (deriv Φ s) (TimeH1.initial hT u)) volume 0 (t : ℝ) :=
    intervalIntegrable_continuous_clm_apply hΦd.continuousOn intervalIntegrable_const
  have hiP : IntervalIntegrable (fun s => (deriv Φ s) (p s)) volume 0 (t : ℝ) :=
    intervalIntegrable_continuous_clm_apply hΦd.continuousOn hp.intervalIntegrable
  have hiV : IntervalIntegrable (fun s => Φ s (TimeH1.velocity u s)) volume 0 (t : ℝ) :=
    intervalIntegrable_continuous_clm_apply hΦ.continuous.continuousOn hvel
  have hconst : (∫ s in (0 : ℝ)..(t : ℝ), (deriv Φ s) (TimeH1.initial hT u)) =
      Φ t (TimeH1.initial hT u) - Φ 0 (TimeH1.initial hT u) := by
    rw [← ContinuousLinearMap.intervalIntegral_apply (hΦd.intervalIntegrable 0 (t : ℝ)),
      intervalIntegral.integral_deriv_eq_sub
        (fun s _ => (hΦ.differentiable one_ne_zero) s) (hΦd.intervalIntegrable _ _)]
    rfl
  have hparts := integral_deriv_clm_primitive_eq_sub_of_le t.property.1 hΦ hvel
  have hsplit : EqOn
      (fun s => (deriv Φ s) (TimeH1.trace hT u (projIcc 0 T hT.le s)) +
        Φ s (TimeH1.velocity u s))
      (fun s => ((deriv Φ s) (TimeH1.initial hT u) + (deriv Φ s) (p s)) +
        Φ s (TimeH1.velocity u s)) (uIcc 0 (t : ℝ)) := by
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans t.property.2⟩
    dsimp only
    rw [projIcc_of_mem hT.le hsT, TimeH1.trace_integral, map_add]
  rw [intervalIntegral.integral_congr hsplit,
    intervalIntegral.integral_add (hiC.add hiP) hiV,
    intervalIntegral.integral_add hiC hiP, hconst]
  change Φ t (TimeH1.trace hT u t) = Φ 0 (TimeH1.initial hT u) +
    ((Φ t (TimeH1.initial hT u) - Φ 0 (TimeH1.initial hT u) +
      (∫ s in (0 : ℝ)..(t : ℝ), (deriv Φ s) (∫ r in (0 : ℝ)..s, TimeH1.velocity u r))) +
        ∫ s in (0 : ℝ)..(t : ℝ), Φ s (TimeH1.velocity u s))
  rw [hparts, TimeH1.trace_integral, map_add]
  abel

/-- Appendix A.3 (`eq:eta_sol`): variation of constants for a bounded
linear operator, valid at both endpoints for the continuous time trace. -/
theorem linear_timeH1_duhamel (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    (f : ℝ → H) (hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T)))
    (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t)
    (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT u t =
      (NormedSpace.exp ((t : ℝ) • A)) (TimeH1.initial hT u) +
        ∫ s in (0 : ℝ)..(t : ℝ), (NormedSpace.exp (((t : ℝ) - s) • A)) (f s) := by
  let : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
  let Φ : ℝ → H →L[ℝ] H := fun s => NormedSpace.exp (s • (-A))
  have hΦc : Continuous Φ :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  have hderiv (s : ℝ) : deriv Φ s = Φ s * (-A) :=
    (hasDerivAt_exp_smul_const (-A) s).deriv
  have hΦ : ContDiff ℝ 1 Φ := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun s => (hasDerivAt_exp_smul_const (-A) s).differentiableAt, ?_⟩
    rw [show deriv Φ = fun s => Φ s * (-A) from funext hderiv]
    exact hΦc.mul continuous_const
  have hfon : IntegrableOn f (Ioo 0 T) := hf.integrable (by norm_num)
  have hfint : IntervalIntegrable f volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le t.property.1).2
      (hfon.mono_set (Ioo_subset_Ioo le_rfl t.property.2))
  have hfi : IntervalIntegrable (fun s => Φ s (f s)) volume 0 (t : ℝ) :=
    intervalIntegrable_continuous_clm_apply hΦc.continuousOn hfint
  have hae : ∀ᵐ s ∂volume.restrict (Icc 0 T),
      (deriv Φ s) (TimeH1.trace hT u (projIcc 0 T hT.le s)) +
        Φ s (TimeH1.velocity u s) = Φ s (f s) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hode, TimeH1.trace_ae hT u] with s hs htr
    rw [hderiv, ← htr, hs, map_add]
    change Φ s (-A (TimeH1.value u s)) + (Φ s (A (TimeH1.value u s)) + Φ s (f s)) = _
    rw [map_neg]
    abel
  have hi : (∫ s in (0 : ℝ)..(t : ℝ),
      (deriv Φ s) (TimeH1.trace hT u (projIcc 0 T hT.le s)) +
        Φ s (TimeH1.velocity u s)) = ∫ s in (0 : ℝ)..(t : ℝ), Φ s (f s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_imp_of_ae_restrict hae] with s hs hst
    rw [uIoc_of_le t.property.1] at hst
    exact hs ⟨hst.1.le, hst.2.trans t.property.2⟩
  have hfactor := timeH1_operator_product_integral hT u hΦ t
  rw [hi] at hfactor
  have hΦzero : Φ 0 = ContinuousLinearMap.id ℝ H := by
    simp only [Φ, zero_smul, NormedSpace.exp_zero]
    rfl
  rw [hΦzero, ContinuousLinearMap.id_apply] at hfactor
  have hsemigroup (r s : ℝ) : NormedSpace.exp (r • A) * NormedSpace.exp (s • A) =
      NormedSpace.exp ((r + s) • A) := by
    rw [add_smul, NormedSpace.exp_add_of_commute
      (((Commute.refl A).smul_left r).smul_right s)]
  have hpair (s : ℝ) (v : H) :
      (NormedSpace.exp ((t : ℝ) • A)) (Φ s v) =
        (NormedSpace.exp (((t : ℝ) - s) • A)) v := by
    change (NormedSpace.exp ((t : ℝ) • A) * NormedSpace.exp (s • (-A))) v = _
    rw [show s • (-A) = (-s) • A by simp, hsemigroup, sub_eq_add_neg]
  have h := congrArg (fun v : H => (NormedSpace.exp ((t : ℝ) • A) : H →L[ℝ] H) v) hfactor
  rw [hpair, sub_self, zero_smul, NormedSpace.exp_zero, one_apply_eq_self,
    map_add, ← (NormedSpace.exp ((t : ℝ) • A)).intervalIntegral_comp_comm hfi] at h
  simpa only [hpair] using h

end KVApproximation.Dynamics
