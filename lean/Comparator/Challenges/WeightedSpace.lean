module

public import KVApproximation.OperatorTheory.WeightedSpace

/-!
# Realization of the coefficient-weighted Hilbert space
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

/-- Section 3.1 and Appendix A.2: the weighted carrier is complete, its
inner product and norm are the prescribed energy, and its continuous linear
identification with the original space is the identity on vectors. -/
theorem weightedSpace_realization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : CoerciveForm H) :
    (∀ u v : WeightedSpace A, ⟪u, v⟫_ℝ = A.form u.val v.val) ∧
      (∀ u : WeightedSpace A, ‖u‖ ^ 2 = A.form u.val u.val) ∧
      CompleteSpace (WeightedSpace A) ∧
      ∃ e : WeightedSpace A ≃L[ℝ] H,
        (∀ u, e u = u.val) ∧ (∀ x, e.symm x = WeightedSpace.mk x) := by
  sorry

end KVApproximation.OperatorTheory
