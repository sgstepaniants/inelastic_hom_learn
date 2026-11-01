module

public import KVApproximation.OperatorTheory.WeightedSpace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Relaxation in the viscous Hilbert space
-/

@[expose] public section

noncomputable section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.2: the corrector space carrying the viscous inner product. -/
abbrev RelaxationSpace (V : CoerciveForm H) (X : ClosedSubmodule ℝ H) :=
  WeightedSpace (V.restrict X)

/-- Appendix A.2: the same relaxation operator in the viscous Hilbert norm. -/
def weightedRelaxation (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    RelaxationSpace V X →L[ℝ] RelaxationSpace V X :=
  (WeightedSpace.continuousLinearEquiv (V.restrict X)).symm.toContinuousLinearMap.comp
    ((relaxation V E X).comp
      (WeightedSpace.continuousLinearEquiv (V.restrict X)).toContinuousLinearMap)

/-- Appendix A.2: the weighted relaxation operator is self-adjoint. -/
theorem weightedRelaxation_isSelfAdjoint (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    IsSelfAdjoint (weightedRelaxation V E X) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  -- Transport changes the norm; the pairing is the restricted viscous form.
  change V.form (relaxation V E X u.val) v.val = V.form u.val (relaxation V E X v.val)
  exact relaxation_selfAdjoint V E X u.val v.val

/-- Appendix A.2: mismatch from macroscopic strains into the viscous Hilbert space. -/
def weightedMismatch {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H) :
    F →L[ℝ] RelaxationSpace V X :=
  (WeightedSpace.continuousLinearEquiv (V.restrict X)).symm.toContinuousLinearMap.comp
    ((mismatch V E X).comp ι)

end KVApproximation.OperatorTheory
