module

public import KVApproximation.Analysis.PeriodicVariation
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Compactness of bounded periodic variation
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Lemma B.2, the divergence test used in the translation estimate. -/
theorem exists_periodic_divergence_eq_translate_sub (g : PeriodicC1 d F)
    (hg : ∀ y, ‖g.value y‖ ≤ 1) (v : EuclideanSpace ℝ (Fin d)) :
    ∃ ψ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F)),
      (∀ y, ‖ψ.value y‖ ≤ ‖v‖) ∧
      ∀ y, ψ.divergence y = g.value (y - toCell v) - g.value y := by
  sorry

/-- Lemma B.2 (`lem:bv_compact`), translation criterion for the cited BV
embedding: translation by a Euclidean vector is controlled by its length and
the original isotropic periodic variation. -/
theorem periodicVariation_translation_bound (A : Lp F 1 (cellMeasure d))
    (h : EuclideanSpace ℝ (Fin d)) :
    eLpNorm (fun y => A (y + toCell h) - A y) 1 (cellMeasure d) ≤
      ENNReal.ofReal ‖h‖ * periodicVariation A := by
  sorry

/-- Lemma B.2 (`lem:bv_compact`): bounded sublevels of the full periodic BV
norm are compact in L¹ for finite-dimensional real inner-product targets. -/
theorem isCompact_periodicBV_sublevel {C : ENNReal} (hC : C ≠ ⊤) :
    IsCompact {A : Lp F 1 (cellMeasure d) | periodicBVNorm A ≤ C} := by
  sorry

end KVApproximation.Analysis
