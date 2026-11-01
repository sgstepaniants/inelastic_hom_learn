module

public import KVApproximation.Tensor.Symmetrization

/-!
# Frobenius contraction under symmetrization
-/

public section

namespace KVApproximation.Tensor

open scoped InnerProductSpace

/-- Theorem 3.1, static flux pairing: a symmetric stress has the same
Frobenius pairing with the full gradient and its symmetric part. -/
theorem inner_symmetrize {d : ℕ} (s : Symmetric d) (g : SecondOrder d) :
    ⟪s, symmetrize g⟫_ℝ = ⟪s.val, g⟫_ℝ := by
  change ⟪s.val, (symmetrize g).val⟫_ℝ = _
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ ij, ((g ij + g (ij.2, ij.1)) / 2) * s.val ij) =
    ∑ ij, g ij * s.val ij
  have ht : (∑ ij, g (ij.2, ij.1) * s.val ij) = ∑ ij, g ij * s.val ij := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [s.property i j]
  calc
    _ = (1 / 2 : ℝ) * (∑ ij, g ij * s.val ij) +
        (1 / 2 : ℝ) * (∑ ij, g (ij.2, ij.1) * s.val ij) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ij _
      ring
    _ = _ := by rw [ht]; ring

/-- Theorem 3.1, strain estimates: taking the symmetric part contracts
the physical-index Frobenius norm, in every dimension. -/
theorem norm_symmetrize_le {d : ℕ} (g : SecondOrder d) :
    ‖symmetrize g‖ ≤ ‖g‖ := by
  let T : SecondOrder d ≃ₗᵢ[ℝ] SecondOrder d :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodComm (Fin d) (Fin d))
  have h : (symmetrize g).val = (1 / 2 : ℝ) • (g + T g) := by
    apply PiLp.ext
    intro ij
    change (g ij + g (ij.2, ij.1)) / 2 = (1 / 2 : ℝ) * (g ij + g (ij.2, ij.1))
    ring
  change ‖(symmetrize g).val‖ ≤ ‖g‖
  rw [h, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht := T.norm_map g
  have ha := norm_add_le g (T g)
  nlinarith

end KVApproximation.Tensor
