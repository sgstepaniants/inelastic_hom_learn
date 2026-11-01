module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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
  sorry

/-- Proposition B.13, trapping argument after `eq:zeta_uniform_bound`:
the finite-time factor keeps the error strictly inside the margin even
when `forcing = rate * margin`. -/
theorem finite_time_decay_lt_margin {rate forcing margin t : ℝ}
    (hRate : 0 < rate) (hforcing : 0 < forcing)
    (hmargin : forcing ≤ rate * margin) :
    forcing / rate * (1 - Real.exp (-rate * t)) < margin := by
  sorry

end KVApproximation.Analysis
