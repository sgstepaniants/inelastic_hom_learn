module

public import KVApproximation.Dynamics.TrajectoryBounds
public import KVApproximation.Analysis.PrimitiveIntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exponential convolutions of trajectory derivatives
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.Dynamics

/-- Lemma B.7, integration by parts: the exponential convolution of the
velocity equals the endpoint terms minus the convolution of the value. -/
theorem BoundedTrajectory.exponential_integral_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →L[ℝ] F) (e : BoundedTrajectory E) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    (∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • J (e.velocity s)) =
      J (e.value t) - Complex.exp (-z * (t : ℂ)) • J (e.value 0) -
        z • ∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • J (e.value s) := by
  let φ : ℝ → ℂ := fun s => Complex.exp (-z * ((t - s : ℝ) : ℂ))
  let v : ℝ → F := fun s => J (e.velocity s)
  let u : ℝ → F := fun s => J (e.value s)
  have hφ : ContDiff ℝ 1 φ :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub contDiff_id))).cexp
  have hd (s : ℝ) : deriv φ s = z * φ s := by
    have hh := ((((hasDerivAt_const s t).sub (hasDerivAt_id s)).ofReal_comp).const_mul (-z)).cexp
    simpa only [φ, Pi.sub_apply, id_eq, Complex.ofReal_zero, Complex.ofReal_one,
      Complex.ofReal_sub, Complex.ofReal_neg, zero_sub, mul_neg, neg_neg,
      mul_one, mul_comm] using hh.deriv
  have hv : IntervalIntegrable v volume 0 t :=
    ⟨J.integrable_comp (e.velocity_intervalIntegrable le_rfl ht).1,
      J.integrable_comp (e.velocity_intervalIntegrable le_rfl ht).2⟩
  have hu (s : ℝ) (hs : 0 ≤ s) : u s = u 0 + ∫ r in (0 : ℝ)..s, v r := by
    change J (e.value s) = J (e.value 0) + ∫ r in (0 : ℝ)..s, J (e.velocity r)
    rw [e.integral_eq s hs, map_add,
      J.intervalIntegral_comp_comm (e.velocity_intervalIntegrable le_rfl hs)]
  have hφd := hφ.continuous_deriv le_rfl
  have hprim := intervalIntegral.continuousOn_primitive_interval
    ((intervalIntegrable_iff' (f := v)).mp hv)
  have hp : (∫ s in (0 : ℝ)..t, deriv φ s • u s) =
      φ t • u t - φ 0 • u 0 - ∫ s in (0 : ℝ)..t, φ s • v s := by
    calc
      _ = ∫ s in (0 : ℝ)..t, deriv φ s • (u 0 + ∫ r in (0 : ℝ)..s, v r) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le ht] at hs
        dsimp only
        rw [hu s hs.1]
      _ = (∫ s in (0 : ℝ)..t, deriv φ s • u 0) +
          ∫ s in (0 : ℝ)..t, deriv φ s • ∫ r in (0 : ℝ)..s, v r := by
        simp_rw [smul_add]
        exact intervalIntegral.integral_add
          ((hφd.smul continuous_const).intervalIntegrable _ _)
          ((hφd.continuousOn.smul hprim).intervalIntegrable)
      _ = (φ t - φ 0) • u 0 +
          (φ t • (∫ r in (0 : ℝ)..t, v r) - ∫ s in (0 : ℝ)..t, φ s • v s) := by
        rw [intervalIntegral.integral_smul_const,
          intervalIntegral.integral_deriv_eq_sub (fun s _ => hφ.differentiable one_ne_zero s)
            (hφd.intervalIntegrable _ _), integral_deriv_smul_primitive_eq_sub_of_le ht hφ hv]
      _ = _ := by
        rw [hu t ht, sub_smul, smul_add]
        abel
  have hφt : φ t = 1 := by simp [φ]
  have hφ0 : φ 0 = Complex.exp (-z * (t : ℂ)) := by simp [φ]
  simp_rw [hd, mul_smul] at hp
  rw [intervalIntegral.integral_smul, hφt, one_smul, hφ0] at hp
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using eq_sub_iff_add_eq.mp hp

end KVApproximation.Dynamics
