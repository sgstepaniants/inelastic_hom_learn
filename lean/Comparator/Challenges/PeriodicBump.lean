module

public import KVApproximation.Analysis.PeriodicSmooth
public import Mathlib.Topology.Algebra.Support

/-!
# Smooth periodic fields supported in a coordinate strip
-/

public section

noncomputable section

namespace KVApproximation.Analysis

/-- Proposition 4.7 (`prop:no_spectral_stability`), localized strains:
a periodic partial derivative vanishes outside the topological support
of the displacement field. The derivative is taken on its Euclidean lift. -/
theorem PeriodicC1.partial_eq_zero_of_notMem_tsupport
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : PeriodicC1 d F) (j : Fin d) {y : PeriodicCell d}
    (hy : y ∉ tsupport φ.value) : φ.partial j y = 0 := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), localized corrector:
every positive-width coordinate strip contains the support of a smooth
periodic scalar bump attaining one and taking values between zero and one. -/
theorem exists_periodic_strip_bump {d : ℕ} (i : Fin d)
    {a : ℝ} (ha : 0 < a) (ha_one : a ≤ 1) :
    ∃ φ : PeriodicC1 d ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => φ.value (toCell x)) ∧
      (∀ y, 0 ≤ φ.value y ∧ φ.value y ≤ 1) ∧
      tsupport φ.value ⊆
        {y : PeriodicCell d | 0 < cellRepresentative y i ∧ cellRepresentative y i < a} ∧
      ∃ y, φ.value y = 1 := by
  sorry

end KVApproximation.Analysis
