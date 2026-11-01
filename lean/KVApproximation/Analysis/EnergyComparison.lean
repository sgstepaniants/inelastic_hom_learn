module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import KVApproximation.Analysis.ACComparison

/-!
# Energy comparison and strict finite-time trapping
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Proposition B.13 (`eq:zeta_uniform_bound`): the Hilbert-space energy
inequality yields the exact norm bound for an absolutely continuous curve,
including times when the curve vanishes. -/
theorem ac_energy_decay_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q v : ℝ → E} {a b rate forcing : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b) (hRate : 0 < rate)
    (hforcing : 0 ≤ forcing)
    (hderiv : ∀ᵐ s ∂volume.restrict (Set.Icc a b), HasDerivAt q (v s) s)
    (henergy : ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      ⟪q s, v s⟫_ℝ ≤ forcing * ‖q s‖ - rate * ‖q s‖ ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ‖q t‖ ≤ ‖q a‖ * Real.exp (-rate * (t - a)) +
      forcing / rate * (1 - Real.exp (-rate * (t - a))) := by
  have hn : AbsolutelyContinuousOnInterval (fun s => ‖q s‖) a b :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hq
  apply ac_linear_decay_bound hn hRate _ ht
  filter_upwards [hderiv, henergy] with s hs he
  by_cases hz : q s = 0
  · have hm : IsLocalMin (fun z => ‖q z‖) s :=
      Filter.Eventually.of_forall (fun z => by
        change ‖q s‖ ≤ ‖q z‖
        rw [hz, norm_zero]
        exact norm_nonneg _)
    rw [hm.deriv_eq_zero, hz, norm_zero, mul_zero, sub_zero]
    exact hforcing
  · have hd := (hs.differentiableAt.norm ℝ hz).hasDerivAt
    have hsq : HasDerivAt (fun z => ‖q z‖ ^ 2)
        (2 * ‖q s‖ * deriv (fun z => ‖q z‖) s) s := by
      convert hd.pow 2 using 1; simp
    have hid := hsq.unique hs.norm_sq
    apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)).mp
    nlinarith

/-- Proposition B.13, trapping argument after `eq:zeta_uniform_bound`:
the finite-time factor keeps the error strictly inside the margin even
when `forcing = rate * margin`. -/
theorem finite_time_decay_lt_margin {rate forcing margin t : ℝ}
    (hRate : 0 < rate) (hforcing : 0 < forcing)
    (hmargin : forcing ≤ rate * margin) :
    forcing / rate * (1 - Real.exp (-rate * t)) < margin := by
  have hpositive : 0 < forcing / rate := div_pos hforcing hRate
  have hstrict : forcing / rate * (1 - Real.exp (-rate * t)) < forcing / rate := by
    nlinarith [mul_pos hpositive (Real.exp_pos (-rate * t))]
  exact hstrict.trans_le ((div_le_iff₀ hRate).mpr (by simpa only [mul_comm] using hmargin))

end KVApproximation.Analysis
