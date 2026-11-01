module

public import KVApproximation.Analysis.PeriodicSmooth
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Smooth periodic tests for the L¹ norm
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Lemma B.2, periodic BV embedding: C¹ periodic fields are dense in L¹.
This is the approximation step used in the smooth-test norm formula. -/
theorem exists_periodicC1_eLpNorm_sub_lt (A : Lp F 1 (cellMeasure d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : PeriodicC1 d F,
      eLpNorm (fun y => A y - φ.value y) 1 (cellMeasure d) < ENNReal.ofReal ε := by
  sorry

/-- Lemma B.2, periodic BV embedding: the L¹ norm is determined by smooth
periodic tests bounded pointwise by one, in the original target norm. -/
theorem eLpNorm_one_eq_iSup_periodicTestPairing (A : Lp F 1 (cellMeasure d)) :
    eLpNorm A 1 (cellMeasure d) =
      ⨆ (φ : PeriodicC1 d F) (_hφ : ∀ y, ‖φ.value y‖ ≤ 1),
        ENNReal.ofReal (∫ y, ⟪A y, φ.value y⟫_ℝ ∂cellMeasure d) := by
  sorry

end KVApproximation.Analysis
