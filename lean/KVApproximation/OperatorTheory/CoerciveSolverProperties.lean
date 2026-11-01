module

public import KVApproximation.OperatorTheory.CoerciveSolvers
public import KVApproximation.OperatorTheory.VariationalStability

/-!
# Variational equations and coercive solution bounds
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, spatial variational operators: the coercive solution
map solves the actual tested equation. -/
theorem CoerciveForm.solveL_spec (A : CoerciveForm H) (f : H →L[ℝ] ℝ) (v : H) :
    A.form (A.solveL f) v = f v := by
  rw [← A.riesz_spec]
  change ⟪A.riesz (A.riesz.symm ((InnerProductSpace.toDual ℝ H).symm f)), v⟫_ℝ = _
  rw [A.riesz.apply_symm_apply]
  exact InnerProductSpace.toDual_symm_apply

/-- Theorem 3.1, spatial evolution: the relative Riesz operator has
the prescribed variational action. -/
theorem relativeRiesz_spec (V E : CoerciveForm H) (u v : H) :
    V.form (relativeRiesz V E u) v = E.form u v := by
  rw [← V.riesz_spec]
  change ⟪V.riesz (V.riesz.symm (E.riesz u)), v⟫_ℝ = _
  rw [V.riesz.apply_symm_apply, E.riesz_spec]

/-- Theorem 3.1 (`eq:two_scale_weak_form`): testing against every vector
is equivalent to the Hilbert-valued evolution equation. -/
theorem variational_equation_iff (V E : CoerciveForm H) (p q : H) (f : H →L[ℝ] ℝ) :
    (∀ v : H, V.form p v + E.form q v = f v) ↔
      p = -relativeRiesz V E q + V.solveL f := by
  have hr (v : H) : V.form (-relativeRiesz V E q + V.solveL f) v =
      f v - E.form q v := by
    rw [map_add, map_neg]
    change -V.form (relativeRiesz V E q) v + V.form (V.solveL f) v = _
    rw [relativeRiesz_spec, V.solveL_spec]
    ring
  constructor
  · intro h
    apply V.eq_of_form_eq
    intro v
    rw [hr]
    exact eq_sub_iff_add_eq.mpr (h v)
  · rintro rfl
    intro v
    rw [hr]
    ring

/-- Theorem 3.1, uniform spatial estimates: a coercivity lower bound
controls the solution of an arbitrary dual load with constant one. -/
theorem CoerciveForm.norm_solveL_le (A : CoerciveForm H) {α : ℝ} (hα : 0 < α)
    (hA : ∀ u : H, α * ‖u‖ ^ 2 ≤ A.form u u) (f : H →L[ℝ] ℝ) :
    ‖A.solveL f‖ ≤ ‖f‖ / α := by
  let z := A.solveL f
  have he : α * ‖z‖ ^ 2 ≤ ‖f‖ * ‖z‖ := by
    calc
      _ ≤ A.form z z := hA z
      _ = f z := A.solveL_spec f z
      _ ≤ ‖f z‖ := le_abs_self _
      _ ≤ _ := f.le_opNorm z
  apply (le_div_iff₀ hα).2
  by_cases hz : ‖z‖ = 0
  · change ‖z‖ * α ≤ ‖f‖
    simpa only [hz, zero_mul] using norm_nonneg f
  · have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    have he' : (‖z‖ * α) * ‖z‖ ≤ ‖f‖ * ‖z‖ := by nlinarith [he]
    exact (mul_le_mul_iff_left₀ hpos).mp he'

/-- Theorem 3.1, uniform spatial generator bound: the relative Riesz
operator is bounded by the elastic upper bound divided by viscous coercivity. -/
theorem relativeRiesz_opNorm_le (V E : CoerciveForm H) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hV : ∀ u : H, α * ‖u‖ ^ 2 ≤ V.form u u)
    (hE : ∀ u : H, E.form u u ≤ β * ‖u‖ ^ 2) :
    ‖relativeRiesz V E‖ ≤ β / α := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hβ hα.le)
  intro u
  have heq : relativeRiesz V E u = V.solveL ((InnerProductSpace.toDual ℝ H) (E.riesz u)) := by
    simp only [relativeRiesz, CoerciveForm.solveL, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply]
  calc
    ‖relativeRiesz V E u‖ = ‖V.solveL ((InnerProductSpace.toDual ℝ H) (E.riesz u))‖ :=
      congrArg norm heq
    _ ≤ ‖(InnerProductSpace.toDual ℝ H) (E.riesz u)‖ / α := V.norm_solveL_le hα hV _
    _ = ‖E.riesz u‖ / α := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ (β * ‖u‖) / α := div_le_div_of_nonneg_right
      ((E.riesz.toContinuousLinearMap.le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (E.riesz_opNorm_le hβ hE) (norm_nonneg u))) hα.le
    _ = (β / α) * ‖u‖ := by ring

end KVApproximation.OperatorTheory
