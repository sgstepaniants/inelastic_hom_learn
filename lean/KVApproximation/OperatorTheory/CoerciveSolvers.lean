module

public import KVApproximation.OperatorTheory.CoerciveForm

/-!
# Coercive solution maps on the whole Hilbert space
-/

@[expose] public section

noncomputable section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, spatial variational operators: the coercive solution
map sends a continuous load functional to its equilibrium displacement. -/
def CoerciveForm.solveL (A : CoerciveForm H) : (H →L[ℝ] ℝ) →L[ℝ] H :=
  A.riesz.symm.toContinuousLinearMap.comp
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Theorem 3.1, spatial evolution: the full-space relative Riesz
operator represents elasticity in the viscous pairing. -/
def relativeRiesz (V E : CoerciveForm H) : H →L[ℝ] H :=
  V.riesz.symm.toContinuousLinearMap.comp E.riesz.toContinuousLinearMap

end KVApproximation.OperatorTheory
