module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp

/-!
# Decay comparison for absolutely continuous trajectories
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition B.13 (`eq:zeta_uniform_bound`), scalar comparison step:
an almost-everywhere differential inequality gives the exact finite-time
decay bound for an absolutely continuous function. -/
theorem ac_linear_decay_bound {f : ℝ → ℝ} {a b rate forcing : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hRate : 0 < rate)
    (hderiv : ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      deriv f s ≤ forcing - rate * f s) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    f t ≤ f a * Real.exp (-rate * (t - a)) +
      forcing / rate * (1 - Real.exp (-rate * (t - a))) := by
  have hft : AbsolutelyContinuousOnInterval f a t := hf.mono (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le (ht.1.trans ht.2)]
    exact Set.Icc_subset_Icc le_rfl ht.2)
  let g : ℝ → ℝ := fun s => Real.exp (rate * (s - a))
  have hg : AbsolutelyContinuousOnInterval g a t :=
    (show ContDiff ℝ 1 g by dsimp only [g]; fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hgd (s : ℝ) : deriv g s = rate * g s := by
    have h : HasDerivAt g (rate * g s) s := by
      simpa only [g, mul_one, mul_comm, id_eq] using
        (((hasDerivAt_id s).sub_const a).const_mul rate).exp
    exact h.deriv
  have hleft : IntervalIntegrable (fun s => deriv f s * g s + f s * deriv g s) volume a t :=
    (hft.intervalIntegrable_deriv.mul_continuousOn hg.continuousOn).add
      (hg.intervalIntegrable_deriv.continuousOn_mul hft.continuousOn)
  have hright : IntervalIntegrable (fun s => forcing * g s) volume a t :=
    (show Continuous (fun s => forcing * g s) by dsimp only [g]; fun_prop).intervalIntegrable a t
  have hAE : ∀ᵐ s ∂volume.restrict (Set.Icc a t),
      deriv f s * g s + f s * deriv g s ≤ forcing * g s := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl ht.2)
      hderiv] with s hs
    rw [hgd]
    have hh := mul_le_mul_of_nonneg_right hs (Real.exp_pos (rate * (s - a))).le
    dsimp only [g] at *
    nlinarith
  have hbound := intervalIntegral.integral_mono_ae_restrict ht.1 hleft hright hAE
  have hIntegral : (∫ s in a..t, forcing * g s) = forcing / rate * (g t - g a) := by
    calc
      _ = ∫ s in a..t, (forcing / rate) * deriv g s := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        rw [hgd]
        field_simp [hRate.ne']
      _ = _ := by rw [intervalIntegral.integral_const_mul, hg.integral_deriv_eq_sub]
  rw [hft.integral_deriv_mul_eq_sub hg, hIntegral] at hbound
  simp only [g, sub_self, mul_zero, Real.exp_zero, mul_one] at hbound
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (rate * (t - a)))).mp
  calc
    f t * Real.exp (rate * (t - a)) ≤
        f a + forcing / rate * (Real.exp (rate * (t - a)) - 1) := by nlinarith
    _ = (f a * Real.exp (-rate * (t - a)) +
          forcing / rate * (1 - Real.exp (-rate * (t - a)))) *
        Real.exp (rate * (t - a)) := by
      rw [neg_mul, Real.exp_neg]
      field_simp [hRate.ne']

end KVApproximation.Analysis
