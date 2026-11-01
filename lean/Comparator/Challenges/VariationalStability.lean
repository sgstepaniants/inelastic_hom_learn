module

public import KVApproximation.OperatorTheory.CoerciveForm

/-!
# Quantitative stability of variational operators
-/

public section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition B.3, upper coefficient bound: a positive symmetric Riesz
operator obeys its quadratic upper bound in operator norm. -/
theorem CoerciveForm.riesz_opNorm_le (A : CoerciveForm H) {β : ℝ}
    (hβ : 0 ≤ β) (hA : ∀ u : H, A.form u u ≤ β * ‖u‖ ^ 2) :
    ‖A.riesz.toContinuousLinearMap‖ ≤ β := by
  sorry

/-- Proposition B.3 (`eq:P_conv`), energy estimate before taking the limit:
the projection difference is controlled by the coefficient difference on
the limiting complementary strain. -/
theorem projection_sub_norm_le (A B : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    {α : ℝ} (hα : 0 < α) (hA : ∀ u : H, α * ‖u‖ ^ 2 ≤ A.form u u) (u : H) :
    ‖A.projection X u - B.projection X u‖ ≤
      ‖A.riesz (B.complement X u) - B.riesz (B.complement X u)‖ / α := by
  sorry

/-- Proposition B.3 (`eq:R_strong`): the two coefficient differences
control the relaxation-operator difference on each fixed corrector. -/
theorem relaxation_sub_norm_le (V₁ E₁ V₀ E₀ : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) {α : ℝ} (hα : 0 < α)
    (hV : ∀ u : H, α * ‖u‖ ^ 2 ≤ V₁.form u u) (u : X) :
    ‖relaxation V₁ E₁ X u - relaxation V₀ E₀ X u‖ ≤
      (‖E₁.riesz (u : H) - E₀.riesz (u : H)‖ +
        ‖V₁.riesz (relaxation V₀ E₀ X u : H) -
          V₀.riesz (relaxation V₀ E₀ X u : H)‖) / α := by
  sorry

/-- Proposition B.3 (`eq:R_uniform_bound`): uniform coercivity and the
elastic upper bound give the dimension-independent relaxation norm bound. -/
theorem relaxation_opNorm_le (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hV : ∀ u : H, α * ‖u‖ ^ 2 ≤ V.form u u)
    (hE : ∀ u : H, E.form u u ≤ β * ‖u‖ ^ 2) :
    ‖relaxation V E X‖ ≤ β / α := by
  sorry

end KVApproximation.OperatorTheory
