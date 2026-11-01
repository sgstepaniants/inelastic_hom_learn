module

public import KVApproximation.OperatorTheory.WeightedRelaxation
public import KVApproximation.OperatorTheory.SemigroupIdentities

/-!
# Symmetry and positivity of the memory form

Appendix A uses self-adjointness in the viscous inner product. Conjugating
the exponential into that Hilbert space supplies the pairing identity. Splitting
the time into two equal parts expresses the memory energy as an elastic energy.
-/

public section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.3: the continuous change of Hilbert norm commutes with the exponential. -/
theorem relaxationSemigroup_conjugate (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (t : ℝ) :
    (WeightedSpace.continuousLinearEquiv (V.restrict X)).symm.conjContinuousAlgEquiv
        (relaxationSemigroup V E X t) =
      NormedSpace.exp (-t • weightedRelaxation V E X) := by
  let : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (RelaxationSpace V X →L[ℝ] RelaxationSpace V X) :=
    .restrictScalars ℚ ℝ _
  let e := (WeightedSpace.continuousLinearEquiv (V.restrict X)).symm.conjContinuousAlgEquiv
  change e (NormedSpace.exp (-t • relaxation V E X)) =
    NormedSpace.exp (-t • e (relaxation V E X))
  rw [NormedSpace.map_exp e e.continuous, map_smul]

/-- Appendix A.3: the exponential is self-adjoint in the viscous pairing. -/
theorem relaxationSemigroup_selfAdjoint (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (t : ℝ) (u v : X) :
    V.form (relaxationSemigroup V E X t u) v =
      V.form u (relaxationSemigroup V E X t v) := by
  have hR := weightedRelaxation_isSelfAdjoint V E X
  have he : IsSelfAdjoint (NormedSpace.exp (-t • weightedRelaxation V E X)) :=
    ((IsSelfAdjoint.all (-t)).smul hR).exp
  rw [← relaxationSemigroup_conjugate V E X t] at he
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp he)
    (WeightedSpace.mk u) (WeightedSpace.mk v)

/-- Appendix A.1: compression of the positive self-adjoint spectral function
`r exp(-t r)` gives a symmetric memory form. -/
theorem memoryForm_symmetric {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H)
    (t : ℝ) (u v : F) :
    memoryForm V E X ι t u v = memoryForm V E X ι t v u := by
  let a := mismatch V E X (ι u)
  let b := mismatch V E X (ι v)
  -- Expand the compression using the underlying corrector vectors.
  change V.form (relaxation V E X (relaxationSemigroup V E X t a)) b =
    V.form (relaxation V E X (relaxationSemigroup V E X t b)) a
  rw [relaxation_selfAdjoint, relaxationSemigroup_selfAdjoint]
  have hc := congrArg (fun T : X →L[ℝ] X => T b) (relaxationSemigroup_commute V E X t)
  change relaxation V E X (relaxationSemigroup V E X t b) =
    relaxationSemigroup V E X t (relaxation V E X b) at hc
  rw [← hc, V.symmetric]

/-- Appendix A.1: the memory form is positive semidefinite at nonnegative times. -/
theorem memoryForm_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H)
    (t : ℝ) (_ht : 0 ≤ t) (u : F) : 0 ≤ memoryForm V E X ι t u u := by
  let a := mismatch V E X (ι u)
  let S := relaxationSemigroup V E X (t / 2)
  have hsplit : relaxationSemigroup V E X t = S.comp S := by
    have ht : t / 2 + t / 2 = t := by ring
    simpa only [ht] using relaxationSemigroup_add V E X (t / 2) (t / 2)
  have hc := congrArg (fun T : X →L[ℝ] X => T (S a))
    (relaxationSemigroup_commute V E X (t / 2))
  change relaxation V E X (S (S a)) = S (relaxation V E X (S a)) at hc
  -- Splitting the semigroup exposes an elastic quadratic form.
  change 0 ≤ V.form (relaxation V E X (relaxationSemigroup V E X t a)) a
  rw [hsplit]
  change 0 ≤ V.form (relaxation V E X (S (S a))) a
  rw [hc, relaxationSemigroup_selfAdjoint, relaxation_spec]
  exact E.nonneg (S a)

end KVApproximation.OperatorTheory
