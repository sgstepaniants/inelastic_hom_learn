module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.OperatorTheory.FieldFormIdentities
public import KVApproximation.OperatorTheory.MemoryIdentities
public import KVApproximation.Tensor.FormRepresentation

/-!
# Tensor representatives of the periodic cell forms

The static forms and the memory form determine their elasticity tensors through
all symmetric-strain pairings. The representing tensors carry the physical-index
Frobenius norm.
-/

public section

noncomputable section

open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Appendix A.1: inserting the localization in both slots makes symmetry explicit. -/
private theorem effectiveForm_symmetric {d : ℕ} (A : CoerciveField d)
    (e f : Symmetric d) : effectiveForm A e f = effectiveForm A f e := by
  change A.toForm.form (constantStrainL d e)
      (A.toForm.complement (correctorSubspace d) (constantStrainL d f)) =
    A.toForm.form (constantStrainL d f)
      (A.toForm.complement (correctorSubspace d) (constantStrainL d e))
  rw [form_complement A.toForm (correctorSubspace d) (constantStrainL d e),
    form_complement A.toForm (correctorSubspace d) (constantStrainL d f)]
  exact A.toForm.symmetric _ _

/-- Appendix A.1: the three tensor components determine the cell model. -/
private theorem model_eq {d : ℕ} {V E : CoerciveField d}
    {C D : CellConstitutiveModel V E}
    (hv : C.viscosity = D.viscosity) (he : C.elasticity = D.elasticity)
    (hk : C.kernel = D.kernel) : C = D := by
  cases C
  cases D
  cases hv
  cases he
  cases hk
  rfl

/-- Appendix A.1: finite-dimensional symmetric forms have unique elasticity-tensor
representatives, defining the two effective tensors and the entire cell kernel. -/
theorem cellConstitutiveModel_exists_unique {d : ℕ} (V E : CoerciveField d) :
    ∃! _C : CellConstitutiveModel V E, True := by
  obtain ⟨Av, hAv, _⟩ := existsUnique_form_tensor (effectiveForm V) (effectiveForm_symmetric V)
  obtain ⟨Ae, hAe, _⟩ := existsUnique_form_tensor (effectiveForm E) (effectiveForm_symmetric E)
  have hK (t : ℝ) : ∃! A : Elasticity d,
      ∀ e f : Symmetric d, ⟪e, action A f⟫_ℝ = cellMemoryForm V E t e f :=
    existsUnique_form_tensor (cellMemoryForm V E t)
      (memoryForm_symmetric V.toForm E.toForm (correctorSubspace d) (constantStrainL d) t)
  let C : CellConstitutiveModel V E :=
    { viscosity := Av
      elasticity := Ae
      kernel := fun t => (hK t).choose
      viscosity_eq := hAv
      elasticity_eq := hAe
      kernel_eq := fun t => (hK t).choose_spec.1 }
  refine ⟨C, trivial, ?_⟩
  intro D _
  apply model_eq
  · apply eq_of_inner_action_eq
    intro e f
    rw [D.viscosity_eq, C.viscosity_eq]
  · apply eq_of_inner_action_eq
    intro e f
    rw [D.elasticity_eq, C.elasticity_eq]
  · funext t
    apply eq_of_inner_action_eq
    intro e f
    rw [D.kernel_eq, C.kernel_eq]

/-- Appendix A.1: the memory tensor is positive semidefinite. -/
theorem cellKernel_nonneg {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) (t : ℝ) (ht : 0 ≤ t) (e : Symmetric d) :
    0 ≤ ⟪e, action (C.kernel t) e⟫_ℝ := by
  rw [C.kernel_eq]
  exact memoryForm_nonneg V.toForm E.toForm (correctorSubspace d) (constantStrainL d) t ht e

/-- Theorem 3.1: the bounded-operator exponential gives a continuous tensor kernel. -/
theorem cellKernel_continuous {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) : Continuous C.kernel := by
  apply continuous_of_inner_action
  intro e f
  simp only [C.kernel_eq]
  let X : ClosedSubmodule ℝ (StrainField d) := correctorSubspace d
  let a := mismatch V.toForm E.toForm X (constantStrainL d e)
  let b := mismatch V.toForm E.toForm X (constantStrainL d f)
  change Continuous (fun t => V.toForm.form
    (relaxation V.toForm E.toForm X (relaxationSemigroup V.toForm E.toForm X t a) :
      StrainField d) b)
  exact (V.toForm.form.continuous.comp
    (X.toSubmodule.subtypeL.continuous.comp
      ((relaxation V.toForm E.toForm X).continuous.comp
        ((relaxationSemigroup_continuous V.toForm E.toForm X).clm_apply continuous_const))))
      |>.clm_apply continuous_const

/-- Remark 1.2: equality of the actual coefficient fields gives zero memory
independently of the chosen bounds and their certificates. -/
theorem cellConstitutiveModel_eq_fields {d : ℕ} (V E : CoerciveField d)
    (hVE : V.field = E.field) (C : CellConstitutiveModel V E) :
    C.viscosity = C.elasticity ∧ ∀ t, C.kernel t = 0 := by
  have hform := CoerciveField.toForm_congr hVE
  constructor
  · apply eq_of_inner_action_eq
    intro e f
    rw [C.viscosity_eq, C.elasticity_eq]
    unfold effectiveForm
    rw [hform]
  · intro t
    apply eq_of_inner_action_eq
    intro e f
    rw [C.kernel_eq]
    unfold cellMemoryForm
    rw [hform, memoryForm_self]
    simp only [zero_apply, action, ZeroMemClass.coe_zero,
      PiLp.zero_apply, zero_mul, Finset.sum_const_zero]
    change 0 = ⟪e.val, (0 : SecondOrder d)⟫_ℝ
    simp

/-- Remark 1.2 (`rem:2`): coincident coefficients give identical effective tensors
and an identically zero memory kernel. -/
theorem cellConstitutiveModel_self {d : ℕ} (A : CoerciveField d)
    (C : CellConstitutiveModel A A) : C.viscosity = C.elasticity ∧ ∀ t, C.kernel t = 0 :=
  cellConstitutiveModel_eq_fields A A rfl C

end KVApproximation.Homogenization
