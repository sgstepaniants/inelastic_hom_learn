module

public import KVApproximation.OperatorTheory.VariationalIdentities
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Quantitative stability of variational operators

Proposition B.3 tests each difference equation by the difference itself.
The estimates below retain that argument on an arbitrary real Hilbert space.
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition B.3, upper coefficient bound: a positive symmetric Riesz
operator obeys its quadratic upper bound in operator norm. -/
theorem CoerciveForm.riesz_opNorm_le (A : CoerciveForm H) {β : ℝ}
    (hβ : 0 ≤ β) (hA : ∀ u : H, A.form u u ≤ β * ‖u‖ ^ 2) :
    ‖A.riesz.toContinuousLinearMap‖ ≤ β := by
  have hsym : A.riesz.toContinuousLinearMap.IsSymmetric := by
    intro u v
    change ⟪A.riesz u, v⟫_ℝ = ⟪u, A.riesz v⟫_ℝ
    calc
      _ = A.form u v := A.riesz_spec u v
      _ = A.form v u := A.symmetric u v
      _ = ⟪A.riesz v, u⟫_ℝ := (A.riesz_spec v u).symm
      _ = _ := real_inner_comm _ _
  rw [A.riesz.toContinuousLinearMap.norm_eq_iSup_rayleighQuotient hsym]
  apply ciSup_le
  intro u
  change |⟪A.riesz u, u⟫_ℝ / ‖u‖ ^ 2| ≤ β
  rw [A.riesz_spec, abs_of_nonneg (div_nonneg (A.nonneg u) (sq_nonneg _))]
  by_cases hu : u = 0
  · simpa [hu] using hβ
  · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hu))).2 (hA u)

omit [CompleteSpace H] in
private theorem norm_le_of_energy_test (A : CoerciveForm H) {α : ℝ}
    (hα : 0 < α) (hA : ∀ u : H, α * ‖u‖ ^ 2 ≤ A.form u u)
    (z f : H) (h : A.form z z = ⟪f, z⟫_ℝ) : ‖z‖ ≤ ‖f‖ / α := by
  have he : α * ‖z‖ ^ 2 ≤ ‖f‖ * ‖z‖ := by
    calc
      _ ≤ A.form z z := hA z
      _ = ⟪f, z⟫_ℝ := h
      _ ≤ _ := real_inner_le_norm f z
  apply (le_div_iff₀ hα).2
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    have he' : (‖z‖ * α) * ‖z‖ ≤ ‖f‖ * ‖z‖ := by nlinarith [he]
    exact (mul_le_mul_iff_left₀ hpos).mp he'

/-- Proposition B.3 (`eq:P_conv`), energy estimate before taking the limit:
the projection difference is controlled by the coefficient difference on
the limiting complementary strain. -/
theorem projection_sub_norm_le (A B : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    {α : ℝ} (hα : 0 < α) (hA : ∀ u : H, α * ‖u‖ ^ 2 ≤ A.form u u) (u : H) :
    ‖A.projection X u - B.projection X u‖ ≤
      ‖A.riesz (B.complement X u) - B.riesz (B.complement X u)‖ / α := by
  let z := A.projection X u - B.projection X u
  have hz : A.form (z : H) z =
      ⟪A.riesz (B.complement X u) - B.riesz (B.complement X u), (z : H)⟫_ℝ := by
    rw [inner_sub_left, A.riesz_spec, B.riesz_spec,
      form_complement_corrector, sub_zero, complement_apply]
    change A.form ((A.projection X u : H) - (B.projection X u : H)) z =
      A.form (u - (B.projection X u : H)) z
    simp only [map_sub, sub_apply]
    rw [form_projection]
  exact norm_le_of_energy_test A hα hA (z : H) _ hz

/-- Proposition B.3 (`eq:R_strong`): the two coefficient differences
control the relaxation-operator difference on each fixed corrector. -/
theorem relaxation_sub_norm_le (V₁ E₁ V₀ E₀ : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) {α : ℝ} (hα : 0 < α)
    (hV : ∀ u : H, α * ‖u‖ ^ 2 ≤ V₁.form u u) (u : X) :
    ‖relaxation V₁ E₁ X u - relaxation V₀ E₀ X u‖ ≤
      (‖E₁.riesz (u : H) - E₀.riesz (u : H)‖ +
        ‖V₁.riesz (relaxation V₀ E₀ X u : H) -
          V₀.riesz (relaxation V₀ E₀ X u : H)‖) / α := by
  let z := relaxation V₁ E₁ X u - relaxation V₀ E₀ X u
  let f := (E₁.riesz (u : H) - E₀.riesz (u : H)) -
    (V₁.riesz (relaxation V₀ E₀ X u : H) - V₀.riesz (relaxation V₀ E₀ X u : H))
  have hz : V₁.form (z : H) z = ⟪f, (z : H)⟫_ℝ := by
    dsimp only [f]
    simp only [inner_sub_left, CoerciveForm.riesz_spec]
    change V₁.form ((relaxation V₁ E₁ X u : H) - (relaxation V₀ E₀ X u : H)) z = _
    simp only [map_sub, sub_apply]
    rw [relaxation_spec, relaxation_spec]
    ring
  exact (norm_le_of_energy_test V₁ hα hV (z : H) f hz).trans
    (div_le_div_of_nonneg_right (norm_sub_le _ _) hα.le)

/-- Proposition B.3 (`eq:R_uniform_bound`): uniform coercivity and the
elastic upper bound give the dimension-independent relaxation norm bound. -/
theorem relaxation_opNorm_le (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hV : ∀ u : H, α * ‖u‖ ^ 2 ≤ V.form u u)
    (hE : ∀ u : H, E.form u u ≤ β * ‖u‖ ^ 2) :
    ‖relaxation V E X‖ ≤ β / α := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hβ hα.le)
  intro u
  have htest : V.form (relaxation V E X u : H) (relaxation V E X u : H) =
      ⟪E.riesz (u : H), (relaxation V E X u : H)⟫_ℝ := by
    rw [relaxation_spec, E.riesz_spec]
  calc
    ‖relaxation V E X u‖ ≤ ‖E.riesz (u : H)‖ / α :=
      norm_le_of_energy_test V hα hV _ _ htest
    _ ≤ (β * ‖u‖) / α := by
      apply div_le_div_of_nonneg_right _ hα.le
      exact (E.riesz.toContinuousLinearMap.le_opNorm (u : H)).trans
        (mul_le_mul_of_nonneg_right (E.riesz_opNorm_le hβ hE) (norm_nonneg _))
    _ = (β / α) * ‖u‖ := by ring

end KVApproximation.OperatorTheory
