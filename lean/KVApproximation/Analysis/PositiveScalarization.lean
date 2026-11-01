module

public import KVApproximation.Analysis.VectorMeasureIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Order

/-!
# Positive scalar tests of vector measures
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition 3.3, uniqueness bridge: a positive scalar test of a vector
measure defines a finite scalar measure, vanishing on variation-null sets. -/
theorem exists_finite_positive_scalarization {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : VectorMeasure X F) (φ : F →L[ℝ] ℝ)
    (hpos : ∀ s : Set X, MeasurableSet s → 0 ≤ φ (ν s)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧
      (∀ s : Set X, MeasurableSet s → μ.real s = φ (ν s)) ∧
      (∀ s : Set X, MeasurableSet s → ν.variation s = 0 → μ s = 0) := by
  let σ : SignedMeasure X := ν.mapRange φ.toAddMonoidHom φ.continuous
  have hσ : 0 ≤[Set.univ] σ := by
    rw [VectorMeasure.restrict_univ, VectorMeasure.restrict_univ]
    intro s hs
    exact hpos s hs
  let μ := σ.toMeasureOfZeroLE Set.univ MeasurableSet.univ hσ
  have hreal (s : Set X) (hs : MeasurableSet s) : μ.real s = φ (ν s) := by
    change μ.real s = σ s
    simpa only [Set.univ_inter] using
      σ.toMeasureOfZeroLE_real_apply hσ MeasurableSet.univ hs
  refine ⟨μ, inferInstance, hreal, fun s hs hz => ?_⟩
  apply (measureReal_eq_zero_iff).1
  rw [hreal s hs, (ν.variation_apply_eq_zero hs).1 hz s Set.Subset.rfl hs, map_zero]

end KVApproximation.Analysis
