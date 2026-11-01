module

public import KVApproximation.OperatorTheory.CoerciveForm
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Variational projection identities
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Appendix A.1: coercivity makes the diagonal energy nonnegative. -/
theorem CoerciveForm.nonneg (A : CoerciveForm H) (u : H) : 0 ≤ A.form u u := by
  obtain ⟨c, hc, hbound⟩ := A.coercive
  exact le_trans (by positivity) (hbound u)

omit [CompleteSpace H] in
/-- Appendix A.1: zero energy characterizes the zero vector. -/
theorem CoerciveForm.energy_eq_zero_iff (A : CoerciveForm H) (u : H) :
    A.form u u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    obtain ⟨c, hc, hbound⟩ := A.coercive
    have h := hbound u
    rw [hu] at h
    have hn : ‖u‖ ≤ 0 := le_of_not_gt fun hn =>
      (not_lt_of_ge h) (mul_pos (mul_pos hc hn) hn)
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg u))
  · rintro rfl
    simp

/-- Section 3.2: the Riesz operator represents the prescribed bilinear form. -/
theorem CoerciveForm.riesz_spec (A : CoerciveForm H) (u v : H) :
    ⟪A.riesz u, v⟫_ℝ = A.form u v :=
  A.coercive.continuousLinearEquivOfBilin_apply u v

/-- Section 3.2 (`eqns:operator_P`): the constructed projection solves
the tested variational equation. -/
theorem form_projection (A : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (u : H) (v : X) :
    A.form (A.projection X u : H) v = A.form u v := by
  calc
    A.form (A.projection X u : H) v =
        ⟪(A.restrict X).riesz (A.projection X u), v⟫_ℝ :=
      ((A.restrict X).riesz_spec _ _).symm
    _ = A.form u v := by
      simp [CoerciveForm.projection, InnerProductSpace.toDual_symm_apply]
      rfl

omit [CompleteSpace H] in
/-- Section 3.2: testing against every vector determines a vector by coercivity. -/
theorem CoerciveForm.eq_of_form_eq (A : CoerciveForm H) {u v : H}
    (h : ∀ w, A.form u w = A.form v w) : u = v := by
  apply sub_eq_zero.mp
  apply (A.energy_eq_zero_iff (u - v)).mp
  calc
    A.form (u - v) (u - v) = A.form u (u - v) - A.form v (u - v) := by
      rw [map_sub A.form u v]
      rfl
    _ = 0 := sub_eq_zero.mpr (h (u - v))

/-- Section 3.2: a variational projection fixes the corrector subspace. -/
theorem projection_eq_self (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u : X) :
    A.projection X u = u := by
  apply (A.restrict X).eq_of_form_eq
  intro v
  exact form_projection A X u v

/-- Section 3.2 (`eq:operator_L`): the constructed relaxation operator
represents elasticity in the viscous pairing. -/
theorem relaxation_spec (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u v : X) :
    V.form (relaxation V E X u : H) v = E.form u v := by
  calc
    V.form (relaxation V E X u : H) v =
        ⟪(V.restrict X).riesz (relaxation V E X u), v⟫_ℝ :=
      ((V.restrict X).riesz_spec _ _).symm
    _ = E.form u v := by
      simp [relaxation, CoerciveForm.riesz_spec]
      rfl

/-- Section 3.2: relaxation is the viscous projection of the relative
Riesz operator, restricted to the corrector subspace. -/
theorem relaxation_eq_projection_riesz (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (u : X) :
    relaxation V E X u = V.projection X (V.riesz.symm (E.riesz (u : H))) := by
  apply (V.restrict X).eq_of_form_eq
  intro v
  -- Both restricted forms are evaluated in the ambient Hilbert space.
  change V.form (relaxation V E X u) v =
    V.form (V.projection X (V.riesz.symm (E.riesz (u : H)))) v
  rw [relaxation_spec, form_projection, ← V.riesz_spec, V.riesz.apply_symm_apply,
    E.riesz_spec]

/-- Appendix A.1: explicit localization by subtraction of the corrector projection. -/
theorem complement_apply (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u : H) :
    A.complement X u = u - (A.projection X u : H) := rfl

/-- Appendix A.1: the corrected strain is orthogonal to the corrector space. -/
theorem form_complement_corrector (A : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (u : H) (v : X) : A.form (A.complement X u) v = 0 := by
  rw [complement_apply, map_sub]
  change A.form u v - A.form (A.projection X u) v = 0
  rw [form_projection, sub_self]

/-- Appendix A.1: the complementary projection has no corrector component. -/
theorem projection_complement (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u : H) :
    A.projection X (A.complement X u) = 0 := by
  rw [complement_apply, map_sub, projection_eq_self, sub_self]

/-- Appendix A.1: the complementary projection is idempotent. -/
theorem complement_idempotent (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u : H) :
    A.complement X (A.complement X u) = A.complement X u := by
  rw [complement_apply, projection_complement]
  simp

/-- Appendix A.1: inserting the complementary projection in both entries
leaves the compressed energy form unchanged. -/
theorem form_complement (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u v : H) :
    A.form u (A.complement X v) =
      A.form (A.complement X u) (A.complement X v) := by
  have hzero : A.form (A.projection X u) (A.complement X v) = 0 := by
    rw [A.symmetric]
    exact form_complement_corrector A X v (A.projection X u)
  conv_rhs => rw [complement_apply A X u, map_sub]
  change A.form u (A.complement X v) =
    A.form u (A.complement X v) - A.form (A.projection X u) (A.complement X v)
  rw [hzero, sub_zero]

/-- Appendix A.1: the complementary projection is self-adjoint in the weighted pairing. -/
theorem complement_selfAdjoint (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u v : H) :
    A.form (A.complement X u) v = A.form u (A.complement X v) := by
  calc
    A.form (A.complement X u) v = A.form v (A.complement X u) := A.symmetric _ _
    _ = A.form (A.complement X v) (A.complement X u) := form_complement A X v u
    _ = A.form (A.complement X u) (A.complement X v) := A.symmetric _ _
    _ = A.form u (A.complement X v) := (form_complement A X u v).symm

/-- Appendix A.1: the complementary energy vanishes precisely on the corrector subspace. -/
theorem form_complement_eq_zero_iff (A : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (u : H) : A.form u (A.complement X u) = 0 ↔ u ∈ X := by
  rw [form_complement, A.energy_eq_zero_iff, complement_apply, sub_eq_zero]
  constructor
  · intro hu
    rw [hu]
    exact (A.projection X u).property
  · intro hu
    exact (congrArg Subtype.val (projection_eq_self A X ⟨u, hu⟩)).symm

/-- Appendix A.2: the complementary energy subtracts the projected energy. -/
theorem complement_energy_eq (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u : H) :
    A.form (A.complement X u) (A.complement X u) =
      A.form u u - A.form (A.projection X u) (A.projection X u) := by
  rw [← form_complement, complement_apply, map_sub, form_projection]

/-- Appendix A.2: the variational projection is a contraction for its own energy. -/
theorem projection_energy_le (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u : H) :
    A.form (A.projection X u) (A.projection X u) ≤ A.form u u := by
  have h := A.nonneg (A.complement X u)
  rw [complement_energy_eq] at h
  exact sub_nonneg.mp h

/-- Appendix A.2: the complementary projection is a contraction for the energy. -/
theorem complement_energy_le (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (u : H) :
    A.form (A.complement X u) (A.complement X u) ≤ A.form u u := by
  rw [complement_energy_eq]
  exact sub_le_self _ (A.nonneg _)

/-- Appendix A.2: relaxation is self-adjoint in the viscous pairing. -/
theorem relaxation_selfAdjoint (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (u v : X) : V.form (relaxation V E X u) v = V.form u (relaxation V E X v) := by
  rw [relaxation_spec, V.symmetric, relaxation_spec, E.symmetric]

/-- Appendix A.2: Rayleigh bounds supporting the common spectral interval. -/
theorem relaxation_energy_bounds (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) (u : X) :
    αE / βV * V.form u u ≤ V.form (relaxation V E X u) u ∧
      V.form (relaxation V E X u) u ≤ βE / αV * V.form u u := by
  rw [relaxation_spec]
  constructor
  · calc
      αE / βV * V.form u u ≤ αE / βV * (βV * ‖(u : H)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hV u).2 (div_nonneg hαE.le hβV.le)
      _ = αE * ‖(u : H)‖ ^ 2 := by rw [← mul_assoc, div_mul_cancel₀ _ hβV.ne']
      _ ≤ E.form u u := (hE u).1
  · calc
      E.form u u ≤ βE * ‖(u : H)‖ ^ 2 := (hE u).2
      _ = βE / αV * (αV * ‖(u : H)‖ ^ 2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hαV.ne']
      _ ≤ βE / αV * V.form u u :=
        mul_le_mul_of_nonneg_left (hV u).1 (div_nonneg hβE.le hαV.le)

/-- Appendix A.2 (`eq:mismatch_bound`): mismatch is the viscous projection
of the elastic complementary strain. -/
theorem mismatch_eq_projection_complement (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (u : H) :
    mismatch V E X u = V.projection X (E.complement X u) := by
  rw [complement_apply, map_sub, projection_eq_self]
  rfl

/-- Appendix A.2 (`eq:mismatch_bound`): the projection contraction and
comparison of the two energies give the quantitative mismatch bound. -/
theorem mismatch_energy_le (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    {αV βV αE βE : ℝ} (hαE : 0 < αE) (hβV : 0 ≤ βV)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) (u : H) :
    V.form (mismatch V E X u) (mismatch V E X u) ≤ βV * βE / αE * ‖u‖ ^ 2 := by
  have hratio : 0 ≤ βV / αE := div_nonneg hβV hαE.le
  rw [mismatch_eq_projection_complement]
  calc
    V.form (V.projection X (E.complement X u)) (V.projection X (E.complement X u)) ≤
        V.form (E.complement X u) (E.complement X u) := projection_energy_le V X _
    _ ≤ βV * ‖E.complement X u‖ ^ 2 := (hV _).2
    _ = βV / αE * (αE * ‖E.complement X u‖ ^ 2) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hαE.ne']
    _ ≤ βV / αE * E.form (E.complement X u) (E.complement X u) :=
      mul_le_mul_of_nonneg_left (hE _).1 hratio
    _ ≤ βV / αE * E.form u u :=
      mul_le_mul_of_nonneg_left (complement_energy_le E X u) hratio
    _ ≤ βV / αE * (βE * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hE u).2 hratio
    _ = βV * βE / αE * ‖u‖ ^ 2 := by ring

end KVApproximation.OperatorTheory
