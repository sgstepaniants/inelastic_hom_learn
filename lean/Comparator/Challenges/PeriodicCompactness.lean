module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Compactness from periodic translations
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.2, compactness criterion for the cited periodic BV embedding:
bounded families with uniformly small Euclidean translation increments have
compact closure in finite-exponent Lp on the cell. -/
theorem isCompact_closure_of_periodic_translations {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {S : Set (Lp F p (cellMeasure d))} {M : ENNReal} (hM : M ≠ ⊤)
    (hbound : ∀ A ∈ S, eLpNorm A p (cellMeasure d) ≤ M)
    (htrans : ∀ ε : ENNReal, 0 < ε → ∃ δ > 0,
      ∀ A ∈ S, ∀ h : EuclideanSpace ℝ (Fin d), ‖h‖ < δ →
        eLpNorm (fun y => A (y + toCell h) - A y) p (cellMeasure d) ≤ ε) :
    IsCompact (closure S) := by
  sorry

end KVApproximation.Analysis
