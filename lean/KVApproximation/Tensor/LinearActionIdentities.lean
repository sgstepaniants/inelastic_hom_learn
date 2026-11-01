module

public import KVApproximation.Tensor.LinearAction

/-!
# Frobenius contraction and symmetry
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.Tensor

/-- Section 2.1: bundling tensor contraction preserves its pointwise action. -/
@[simp]
theorem actionL_apply {d : ℕ} (A : Elasticity d) (e : Symmetric d) :
    actionL d A e = action A e := rfl

/-- Section 2.1: fourth-order Frobenius contraction is bounded with constant one. -/
theorem norm_action_le {d : ℕ} (A : Elasticity d) (e : Symmetric d) :
    ‖action A e‖ ≤ ‖A‖ * ‖e‖ := by
  have hsq : ‖action A e‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖e‖ ^ 2 := by
    -- Subtype norms are the ambient Frobenius norms.
    change ‖(action A e).val‖ ^ 2 ≤ ‖A.val‖ ^ 2 * ‖e.val‖ ^ 2
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    -- Apply Cauchy–Schwarz to each contraction row, then sum the rows.
    change (∑ ij, (∑ kl, A.val (ij, kl) * e.val kl) ^ 2) ≤
      (∑ p, A.val p ^ 2) * (∑ kl, e.val kl ^ 2)
    calc
      _ ≤ ∑ ij : Fin d × Fin d,
          (∑ kl : Fin d × Fin d, A.val (ij, kl) ^ 2) *
            (∑ kl : Fin d × Fin d, e.val kl ^ 2) := by
        apply Finset.sum_le_sum
        intro ij _
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun kl => A.val (ij, kl))
          (fun kl => e.val kl)
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        exact (Fintype.sum_prod_type
          (fun p : (Fin d × Fin d) × (Fin d × Fin d) => A.val p ^ 2)).symm
  have hnonneg : 0 ≤ ‖A‖ * ‖e‖ := mul_nonneg (norm_nonneg A) (norm_nonneg e)
  nlinarith [norm_nonneg (action A e)]

/-- Section 3.1: major tensor symmetry gives a symmetric energy pairing. -/
theorem action_symmetric {d : ℕ} (A : Elasticity d) (e f : Symmetric d) :
    ⟪action A e, f⟫_ℝ = ⟪e, action A f⟫_ℝ := by
  -- The symmetry subspaces inherit their ambient Frobenius inner products.
  change ⟪(action A e).val, f.val⟫_ℝ = ⟪e.val, (action A f).val⟫_ℝ
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  -- Expand the two contractions over their ordered physical indices.
  change (∑ ij, f.val ij * ∑ kl, A.val (ij, kl) * e.val kl) =
    ∑ ij, (∑ kl, A.val (ij, kl) * f.val kl) * e.val ij
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij _
  apply Finset.sum_congr rfl
  intro kl _
  rw [(A.property kl.1 kl.2 ij.1 ij.2).2.2]
  ring

end KVApproximation.Tensor
