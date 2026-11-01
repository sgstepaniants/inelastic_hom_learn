module

public import KVApproximation.OperatorTheory.MemoryKernel

/-!
# Elementary relaxation semigroup identities
-/

public section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Section 3.2: the exponential is the identity at time zero. -/
theorem relaxationSemigroup_zero (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    relaxationSemigroup V E X 0 = ContinuousLinearMap.id ℝ X.toSubmodule := by
  have hzero : -(0 : ℝ) • relaxation V E X = 0 := by
    ext u
    simp
  unfold relaxationSemigroup
  rw [hzero]
  exact NormedSpace.exp_zero

/-- Section 3.2: the bounded-operator exponential satisfies the semigroup identity. -/
theorem relaxationSemigroup_add (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (s t : ℝ) : relaxationSemigroup V E X (s + t) =
      (relaxationSemigroup V E X s).comp (relaxationSemigroup V E X t) := by
  -- The exponential convergence theorem uses the induced rational normed algebra.
  let : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  unfold relaxationSemigroup
  have hadd : -(s + t) • relaxation V E X =
      -s • relaxation V E X + -t • relaxation V E X := by
    ext u
    simp [add_smul, add_comm]
  rw [hadd]
  apply NormedSpace.exp_add_of_commute
  -- Multiplication in the endomorphism algebra is composition.
  change (-s • relaxation V E X).comp (-t • relaxation V E X) =
    (-t • relaxation V E X).comp (-s • relaxation V E X)
  ext u
  simp [ContinuousLinearMap.comp_apply, smul_smul, mul_comm]

/-- Appendix A.3: relaxation commutes with its exponential. -/
theorem relaxationSemigroup_commute (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (t : ℝ) : (relaxation V E X).comp (relaxationSemigroup V E X t) =
      (relaxationSemigroup V E X t).comp (relaxation V E X) := by
  have h : Commute (relaxation V E X) (-t • relaxation V E X) := by
    -- Express algebraic commutation as equality of compositions.
    change (relaxation V E X).comp (-t • relaxation V E X) =
      (-t • relaxation V E X).comp (relaxation V E X)
    ext u
    simp [ContinuousLinearMap.comp_apply]
  exact h.exp_right.eq

/-- Section 3.2: a bounded generator gives continuity in operator norm,
and therefore a strongly continuous relaxation semigroup. -/
theorem relaxationSemigroup_continuous (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    Continuous (relaxationSemigroup V E X) := by
  -- Use the same rational normed algebra as in the addition identity.
  let : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)

/-- Remark 1.2 (`rem:2`): identical viscous and elastic forms have zero mismatch. -/
theorem mismatch_self (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    mismatch A A X = 0 := by
  simp [mismatch]

/-- Remark 1.2 (`rem:2`): identical viscous and elastic forms generate no memory. -/
theorem memoryForm_self {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H) (t : ℝ) :
    memoryForm A A X ι t = 0 := by
  ext u v
  simp [memoryForm, mismatch_self]

end KVApproximation.OperatorTheory
