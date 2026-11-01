module

public import KVApproximation.OperatorTheory.VariationalIdentities
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# The Hilbert norm induced by a coercive form
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Section 3.1: a separate carrier for the coefficient-weighted Hilbert norm. -/
structure WeightedSpace (A : CoerciveForm H) where
  /-- The underlying vector in the unweighted space. -/
  val : H

namespace WeightedSpace

variable (A : CoerciveForm H)

/-- Section 3.1: weighted and unweighted spaces have the same vectors. -/
def equiv : WeightedSpace A ≃ H where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (WeightedSpace A) := (equiv A).addCommGroup
instance : SMul ℝ (WeightedSpace A) := (equiv A).smul ℝ

/-- Section 3.1: the identity of the underlying additive groups. -/
def addEquiv : WeightedSpace A ≃+ H where
  __ := equiv A
  map_add' _ _ := rfl

-- Retain the scalar action already transferred by `equiv`.
instance : Module ℝ (WeightedSpace A) :=
  Function.Injective.module ℝ (addEquiv A).toAddMonoidHom (addEquiv A).injective
    (fun _ _ => rfl)

/-- Section 3.1: changing the energy leaves the linear structure unchanged. -/
def linearEquiv : WeightedSpace A ≃ₗ[ℝ] H where
  __ := addEquiv A
  map_smul' _ _ := rfl

instance innerCore : InnerProductSpace.Core ℝ (WeightedSpace A) where
  inner u v := A.form u.val v.val
  conj_inner_symm u v := by simpa using A.symmetric v.val u.val
  re_inner_nonneg u := A.nonneg u.val
  add_left u v w := by
    -- The transferred addition is the original vector addition.
    change A.form (u.val + v.val) w.val = A.form u.val w.val + A.form v.val w.val
    simp
  smul_left u v r := by
    -- The transferred scalar action is the original real scalar action.
    change A.form (r • u.val) v.val = r * A.form u.val v.val
    simp
  definite u hu := (equiv A).injective ((A.energy_eq_zero_iff u.val).mp hu)

instance : NormedAddCommGroup (WeightedSpace A) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance : InnerProductSpace ℝ (WeightedSpace A) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (WeightedSpace A))

-- Expose the canonical parent directly for nested operator-space instances.
instance : NormedSpace ℝ (WeightedSpace A) :=
  (inferInstance : InnerProductSpace ℝ (WeightedSpace A)).toNormedSpace

/-- Section 3.1: the new inner product is the prescribed energy pairing. -/
theorem inner_eq (u v : WeightedSpace A) : ⟪u, v⟫_ℝ = A.form u.val v.val := rfl

/-- Section 3.1: the weighted norm is the square root of the energy. -/
theorem norm_eq (u : WeightedSpace A) : ‖u‖ = Real.sqrt (A.form u.val u.val) := rfl

/-- Section 3.1: the weighted norm squared is exactly the energy. -/
theorem norm_sq (u : WeightedSpace A) : ‖u‖ ^ 2 = A.form u.val u.val :=
  (real_inner_self_eq_norm_sq u).symm

/-- Section 3.1: boundedness of the form controls the weighted norm. -/
theorem norm_le (u : WeightedSpace A) : ‖u‖ ≤ Real.sqrt ‖A.form‖ * ‖u.val‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [norm_sq, mul_pow, Real.sq_sqrt (norm_nonneg A.form)]
  calc
    A.form u.val u.val ≤ ‖A.form u.val u.val‖ := Real.le_norm_self _
    _ ≤ ‖A.form‖ * ‖u.val‖ * ‖u.val‖ := A.form.le_opNorm₂ _ _
    _ = ‖A.form‖ * ‖u.val‖ ^ 2 := by ring

/-- Section 3.1: coercivity controls the original norm by the weighted norm. -/
theorem exists_norm_val_le : ∃ C : ℝ, 0 < C ∧
    ∀ u : WeightedSpace A, ‖u.val‖ ≤ C * ‖u‖ := by
  obtain ⟨c, hc, hbound⟩ := A.coercive
  refine ⟨(Real.sqrt c)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hc), ?_⟩
  intro u
  have h := Real.sqrt_le_sqrt (hbound u.val)
  rw [mul_assoc, ← pow_two, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _),
    ← norm_eq] at h
  exact (le_inv_mul_iff₀ (Real.sqrt_pos.mpr hc)).mpr h

/-- Section 3.1: the weighted and unweighted norms induce the same topology. -/
def continuousLinearEquiv : WeightedSpace A ≃L[ℝ] H :=
  (linearEquiv A).toContinuousLinearEquivOfBounds
    (Classical.choose (exists_norm_val_le A)) (Real.sqrt ‖A.form‖)
    (Classical.choose_spec (exists_norm_val_le A)).2
    (fun u => norm_le A ⟨u⟩)

/-- Section 3.1: the weighted identity preserves the vector, not its original norm. -/
theorem continuousLinearEquiv_apply (u : WeightedSpace A) :
    continuousLinearEquiv A u = u.val := rfl

/-- Section 3.1: the inverse weighted identity is the canonical inclusion. -/
theorem continuousLinearEquiv_symm_apply (u : H) :
    (continuousLinearEquiv A).symm u = mk u := rfl

/-- Section 3.1: norm equivalence also identifies the two uniform structures. -/
def uniformEquiv : WeightedSpace A ≃ᵤ H where
  toEquiv := (continuousLinearEquiv A).toEquiv
  uniformContinuous_toFun := (continuousLinearEquiv A).toContinuousLinearMap.uniformContinuous
  uniformContinuous_invFun :=
    (continuousLinearEquiv A).symm.toContinuousLinearMap.uniformContinuous

instance [CompleteSpace H] : CompleteSpace (WeightedSpace A) :=
  (uniformEquiv A).completeSpace_iff.mpr inferInstance

end WeightedSpace

end KVApproximation.OperatorTheory
