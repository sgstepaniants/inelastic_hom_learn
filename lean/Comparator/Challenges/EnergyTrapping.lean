module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Trapping by a conditional energy inequality
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Proposition B.13 (`eq:zeta_uniform_bound`), first-exit argument:
an energy estimate valid inside the closed error tube keeps the curve
strictly inside that tube and gives the exact finite-time error bound. -/
theorem ac_energy_trapping_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q v : ℝ → E} {a b rate forcing margin : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b) (hq₀ : q a = 0)
    (hRate : 0 < rate) (hforcing : 0 < forcing) (hMargin : 0 < margin)
    (hmargin : forcing ≤ rate * margin)
    (hderiv : ∀ᵐ s ∂volume.restrict (Set.Icc a b), HasDerivAt q (v s) s)
    (henergy : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ‖q s‖ ≤ margin →
      ⟪q s, v s⟫_ℝ ≤ forcing * ‖q s‖ - rate * ‖q s‖ ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ‖q t‖ ≤ forcing / rate * (1 - Real.exp (-rate * (t - a))) ∧ ‖q t‖ < margin := by
  sorry

end KVApproximation.Analysis
