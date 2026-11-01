module

public import KVApproximation.OperatorTheory.CoerciveSolvers

public section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, spatial variational operators: the coercive solution
map solves the actual tested equation. -/
theorem CoerciveForm.solveL_spec (A : CoerciveForm H) (f : H →L[ℝ] ℝ) (v : H) :
    A.form (A.solveL f) v = f v := by
  sorry

/-- Theorem 3.1, spatial evolution: the relative Riesz operator has
the prescribed variational action. -/
theorem relativeRiesz_spec (V E : CoerciveForm H) (u v : H) :
    V.form (relativeRiesz V E u) v = E.form u v := by
  sorry

/-- Theorem 3.1 (`eq:two_scale_weak_form`): testing against every vector
is equivalent to the Hilbert-valued evolution equation. -/
theorem variational_equation_iff (V E : CoerciveForm H) (p q : H) (f : H →L[ℝ] ℝ) :
    (∀ v : H, V.form p v + E.form q v = f v) ↔
      p = -relativeRiesz V E q + V.solveL f := by
  sorry

/-- Theorem 3.1, uniform spatial estimates: a coercivity lower bound
controls the solution of an arbitrary dual load with constant one. -/
theorem CoerciveForm.norm_solveL_le (A : CoerciveForm H) {α : ℝ} (hα : 0 < α)
    (hA : ∀ u : H, α * ‖u‖ ^ 2 ≤ A.form u u) (f : H →L[ℝ] ℝ) :
    ‖A.solveL f‖ ≤ ‖f‖ / α := by
  sorry

/-- Theorem 3.1, uniform spatial generator bound: the relative Riesz
operator is bounded by the elastic upper bound divided by viscous coercivity. -/
theorem relativeRiesz_opNorm_le (V E : CoerciveForm H) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hV : ∀ u : H, α * ‖u‖ ^ 2 ≤ V.form u u)
    (hE : ∀ u : H, E.form u u ≤ β * ‖u‖ ^ 2) :
    ‖relativeRiesz V E‖ ≤ β / α := by
  sorry

end KVApproximation.OperatorTheory
