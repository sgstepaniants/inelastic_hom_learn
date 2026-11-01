module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Coercive forms and variational projections

All operators act on the fixed underlying Hilbert space. The form determines
the variational projection and the relative relaxation operator.
-/

@[expose] public section

noncomputable section

namespace KVApproximation.OperatorTheory

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Section 3.1, weighted inner products: a bounded symmetric coercive
form on a real Hilbert space. -/
structure CoerciveForm where
  form : H →L[ℝ] H →L[ℝ] ℝ
  symmetric : ∀ u v, form u v = form v u
  coercive : IsCoercive form

variable {H}

/-- Proposition 3.3 (`eq:constants_spectral_rep`): quantitative lower and
upper bounds relative to the fixed underlying Hilbert norm. -/
def CoerciveForm.HasBounds (A : CoerciveForm H) (α β : ℝ) : Prop :=
  ∀ u : H, α * ‖u‖ ^ 2 ≤ A.form u u ∧ A.form u u ≤ β * ‖u‖ ^ 2

/-- Section 3.2 (`eq:operator_L`): restriction of a coercive form to a
closed Hilbert subspace. -/
def CoerciveForm.restrict (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    CoerciveForm X where
  form := A.form.bilinearComp X.toSubmodule.subtypeL X.toSubmodule.subtypeL
  symmetric u v := A.symmetric u v
  coercive := by
    obtain ⟨c, hc, hbound⟩ := A.coercive
    exact ⟨c, hc, fun u => hbound u⟩

variable [CompleteSpace H]

/-- Section 3.2: the invertible Riesz operator of a coercive form,
constructed by the Lax–Milgram theorem. -/
def CoerciveForm.riesz (A : CoerciveForm H) : H ≃L[ℝ] H :=
  A.coercive.continuousLinearEquivOfBilin

/-- Section 3.2 (`eqns:operator_P`): the variational projection onto a
closed subspace, constructed from the restricted Riesz operator. -/
def CoerciveForm.projection (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    H →L[ℝ] X :=
  (A.restrict X).riesz.symm.toContinuousLinearMap.comp
    ((InnerProductSpace.toDual ℝ X).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (A.form.bilinearComp (ContinuousLinearMap.id ℝ H) X.toSubmodule.subtypeL))

/-- Section 3.2: the complementary localization operator `Id − P`. -/
def CoerciveForm.complement (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - X.toSubmodule.subtypeL.comp (A.projection X)

/-- Section 3.2 (`eq:operator_L`): the relative relaxation operator,
the composition of the inverse viscous Riesz operator with the elastic Riesz operator. -/
def relaxation (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) : X →L[ℝ] X :=
  (V.restrict X).riesz.symm.toContinuousLinearMap.comp
    (E.restrict X).riesz.toContinuousLinearMap

/-- Section 3.2: mismatch between the viscous and elastic projections. -/
def mismatch (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) : H →L[ℝ] X :=
  V.projection X - E.projection X

/-- Theorem 3.1 (`eq:homogenized_tensors`): the compressed complementary
form, with `ι` the embedding of the finite-dimensional macroscopic strains. -/
def CoerciveForm.homogenizedForm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H) :
    F →L[ℝ] F →L[ℝ] ℝ :=
  A.form.bilinearComp ι ((A.complement X).comp ι)

end KVApproximation.OperatorTheory
