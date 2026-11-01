module

public import KVApproximation.Tensor.FormRepresentation
public import KVApproximation.Tensor.Dimensions
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Operator and Frobenius bounds for elasticity tensors
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.Tensor

/-- Lemma B.2 and Proposition B.3: the positive tensor action has the quadratic upper
bound as an operator-norm bound. -/
theorem HasBounds.action_opNorm_le {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : HasBounds α β A) :
    ‖actionL d A‖ ≤ β := by
  have hsym : (actionL d A).IsSymmetric := fun e f => action_symmetric A e f
  rw [(actionL d A).norm_eq_iSup_rayleighQuotient hsym]
  apply ciSup_le
  intro e
  change |⟪action A e, e⟫_ℝ / ‖e‖ ^ 2| ≤ β
  rw [real_inner_comm]
  have hpos : 0 ≤ ⟪e, action A e⟫_ℝ :=
    (mul_nonneg hα (sq_nonneg _)).trans (hA e).1
  rw [abs_of_nonneg (div_nonneg hpos (sq_nonneg _))]
  by_cases he : e = 0
  · simpa [he] using hβ
  · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr he))).2 (hA e).2

/-- Proposition B.3: the same upper bound controls the action on each strain. -/
theorem HasBounds.norm_action_le {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : HasBounds α β A) (e : Symmetric d) :
    ‖action A e‖ ≤ β * ‖e‖ := by
  exact ((actionL d A).le_opNorm e).trans
    (mul_le_mul_of_nonneg_right (hA.action_opNorm_le hα hβ) (norm_nonneg e))

/-- Lemma B.2 (`lem:bv_compact`), coefficient bound: the exact Frobenius
factor is the square root of the symmetric-strain dimension. -/
theorem HasBounds.norm_le_sqrt_dimension {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : HasBounds α β A) :
    ‖A‖ ≤ Real.sqrt (strainDimension d) * β := by
  let b := stdOrthonormalBasis ℝ (Symmetric d)
  have hsq : ‖A‖ ^ 2 ≤ (strainDimension d : ℝ) * β ^ 2 := by
    rw [norm_sq_eq_sum_norm_action b A]
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (Symmetric d)), β ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := hA.norm_action_le hα hβ (b i)
        rw [b.norm_eq_one, mul_one] at h
        exact (sq_le_sq₀ (norm_nonneg _) hβ).2 h
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, finrank_symmetric]
  apply (sq_le_sq₀ (norm_nonneg A) (mul_nonneg (Real.sqrt_nonneg _) hβ)).mp
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (strainDimension d))] using hsq

end KVApproximation.Tensor
