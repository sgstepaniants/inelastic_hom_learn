module

public import KVApproximation.OperatorTheory.VariationalIdentities

/-!
# Energy bounds for compressed variational forms
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.1: isometric compression orthogonal to the corrector space
preserves the original lower and upper energy bounds. -/
theorem CoerciveForm.homogenizedForm_bounds
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H)
    (hι : ∀ e, ‖ι e‖ = ‖e‖) (horth : ∀ e (x : X), ⟪ι e, (x : H)⟫_ℝ = 0)
    {α β : ℝ} (hα : 0 ≤ α) (hA : A.HasBounds α β) (e : F) :
    α * ‖e‖ ^ 2 ≤ A.homogenizedForm X ι e e ∧
      A.homogenizedForm X ι e e ≤ β * ‖e‖ ^ 2 := by
  change α * ‖e‖ ^ 2 ≤ A.form (ι e) (A.complement X (ι e)) ∧
    A.form (ι e) (A.complement X (ι e)) ≤ β * ‖e‖ ^ 2
  rw [form_complement]
  have hnorm : ‖e‖ ^ 2 ≤ ‖A.complement X (ι e)‖ ^ 2 := by
    rw [complement_apply, norm_sub_sq_real, horth, hι, mul_zero, sub_zero]
    exact le_add_of_nonneg_right (sq_nonneg _)
  constructor
  · exact (mul_le_mul_of_nonneg_left hnorm hα).trans (hA _).1
  · calc
      A.form (A.complement X (ι e)) (A.complement X (ι e)) ≤
          A.form (ι e) (ι e) := complement_energy_le A X (ι e)
      _ ≤ β * ‖ι e‖ ^ 2 := (hA _).2
      _ = β * ‖e‖ ^ 2 := by rw [hι]

end KVApproximation.OperatorTheory
