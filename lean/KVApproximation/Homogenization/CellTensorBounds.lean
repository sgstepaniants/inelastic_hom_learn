module

public import KVApproximation.Homogenization.StaticCellOperators
public import KVApproximation.Homogenization.ConstantStrainIdentities
public import KVApproximation.Homogenization.CorrectorOrthogonality
public import KVApproximation.OperatorTheory.HomogenizedBounds

/-!
# Norm estimates for the cell tensors
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor
open KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Appendix A.1: effective coefficients preserve the stated ellipticity bounds. -/
theorem effectiveForm_bounds {d : ℕ} (A : CoerciveField d) {α β : ℝ}
    (hα : 0 < α) (hA : HasFieldBounds α β A.field) (e : Symmetric d) :
    α * ‖e‖ ^ 2 ≤ effectiveForm A e e ∧ effectiveForm A e e ≤ β * ‖e‖ ^ 2 := by
  have hA' : A.toForm.HasBounds α β := by
    simpa only [CoerciveForm.HasBounds, HasFieldBounds, CoerciveField.toForm,
      boundedFieldForm_apply] using hA
  exact A.toForm.homogenizedForm_bounds (correctorSubspace d) (constantStrainL d)
    norm_constantStrain constantStrain_orthogonal_corrector hα.le hA' e

/-- Appendix A.1: the effective tensor is positive definite, since constant
strains are orthogonal to the periodic corrector subspace. -/
theorem effectiveForm_pos {d : ℕ} (A : CoerciveField d) (e : Symmetric d) (he : e ≠ 0) :
    0 < effectiveForm A e e := by
  change 0 < A.toForm.form (constantStrainL d e)
    (A.toForm.complement (correctorSubspace d) (constantStrainL d e))
  have hn : 0 ≤ A.toForm.form (constantStrainL d e)
      (A.toForm.complement (correctorSubspace d) (constantStrainL d e)) := by
    rw [form_complement]
    exact A.toForm.nonneg _
  apply lt_of_le_of_ne hn
  intro hz
  have hmem := (form_complement_eq_zero_iff A.toForm (correctorSubspace d)
    (constantStrainL d e)).mp hz.symm
  have horth := constantStrain_orthogonal_corrector e ⟨constantStrainL d e, hmem⟩
  change ⟪constantStrainL d e, constantStrainL d e⟫_ℝ = 0 at horth
  rw [real_inner_self_eq_norm_sq (constantStrainL d e), norm_constantStrain] at horth
  exact he (norm_eq_zero.mp (sq_eq_zero_iff.mp horth))

end KVApproximation.Homogenization
