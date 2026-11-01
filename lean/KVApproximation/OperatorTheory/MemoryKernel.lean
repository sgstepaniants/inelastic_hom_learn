module

public import KVApproximation.OperatorTheory.CoerciveForm
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Relaxation semigroups and compressed memory forms
-/

@[expose] public section

noncomputable section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Section 3.2: the bounded relaxation semigroup `exp(-t R)`. -/
def relaxationSemigroup (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (t : ℝ) : X →L[ℝ] X :=
  NormedSpace.exp (-t • relaxation V E X)

/-- Theorem 3.1 (`eq:memory_kernel`): compression of `R exp(-t R)`
through the mismatch operator, using the viscous energy pairing. -/
def memoryForm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H)
    (t : ℝ) : F →L[ℝ] F →L[ℝ] ℝ :=
  (V.restrict X).form.bilinearComp
    ((relaxation V E X).comp
      ((relaxationSemigroup V E X t).comp ((mismatch V E X).comp ι)))
    ((mismatch V E X).comp ι)

end KVApproximation.OperatorTheory
