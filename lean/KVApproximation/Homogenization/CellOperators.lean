module

public import KVApproximation.Homogenization.StaticCellOperators
public import KVApproximation.OperatorTheory.MemoryKernel

/-!
# Operators of the periodic cell problem
-/

@[expose] public section

noncomputable section

open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Section 3.2 (`eq:operator_L`): the relative viscous–elastic relaxation operator. -/
def cellRelaxation {d : ℕ} (V E : CoerciveField d) :
    correctorSubspace d →L[ℝ] correctorSubspace d :=
  OperatorTheory.relaxation V.toForm E.toForm (correctorSubspace d)

/-- Section 3.2: mismatch between viscous and elastic cell projections. -/
def cellMismatch {d : ℕ} (V E : CoerciveField d) :
    StrainField d →L[ℝ] correctorSubspace d :=
  OperatorTheory.mismatch V.toForm E.toForm (correctorSubspace d)

/-- Theorem 3.1 (`eq:memory_kernel`): the actual periodic-cell memory form. -/
def cellMemoryForm {d : ℕ} (V E : CoerciveField d) (t : ℝ) :
    Symmetric d →L[ℝ] Symmetric d →L[ℝ] ℝ :=
  OperatorTheory.memoryForm V.toForm E.toForm (correctorSubspace d)
    (constantStrainL d) t

/-- Theorem 3.1: tensors representing the two static cell forms and
the time-dependent memory form. These identities fix every tensor component. -/
structure CellConstitutiveModel {d : ℕ} (V E : CoerciveField d) where
  viscosity : Elasticity d
  elasticity : Elasticity d
  kernel : ℝ → Elasticity d
  viscosity_eq : ∀ e f : Symmetric d,
    ⟪e, action viscosity f⟫_ℝ = effectiveForm V e f
  elasticity_eq : ∀ e f : Symmetric d,
    ⟪e, action elasticity f⟫_ℝ = effectiveForm E e f
  kernel_eq : ∀ (t : ℝ) (e f : Symmetric d),
    ⟪e, action (kernel t) f⟫_ℝ = cellMemoryForm V E t e f

end KVApproximation.Homogenization
