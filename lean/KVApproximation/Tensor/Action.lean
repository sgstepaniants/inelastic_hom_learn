module

public import KVApproximation.Tensor.Spaces

/-!
# Tensor contraction and ellipticity
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace KVApproximation.Tensor

/-- Section 2.1 (`main.tex:171`): contraction of a fourth-order tensor
with a symmetric strain over its last two physical indices. -/
def action {d : ℕ} (A : Elasticity d) (e : Symmetric d) : Symmetric d :=
  ⟨WithLp.toLp 2 (fun ij => ∑ kl : Fin d × Fin d, A.1 (ij, kl) * e.1 kl), by
    intro i j
    change (∑ kl : Fin d × Fin d, A.1 ((i, j), kl) * e.1 kl) =
      ∑ kl : Fin d × Fin d, A.1 ((j, i), kl) * e.1 kl
    apply Finset.sum_congr rfl
    rintro ⟨k, l⟩ _
    rw [(A.property i j k l).1]⟩

/-- Section 2.1 (`main.tex:171`): the positive-definite cone `𝒱⁴₊`.
For a field, the lower bound must be uniform in the spatial variable. -/
def PositiveDefinite {d : ℕ} (A : Elasticity d) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ e : Symmetric d, α * ‖e‖ ^ 2 ≤ ⟪e, action A e⟫_ℝ

/-- Proposition 3.3 (`eq:constants_spectral_rep`): pointwise lower and
upper quadratic-form bounds, prior to integration over the unit cell. -/
def HasBounds {d : ℕ} (α β : ℝ) (A : Elasticity d) : Prop :=
  ∀ e : Symmetric d,
    α * ‖e‖ ^ 2 ≤ ⟪e, action A e⟫_ℝ ∧ ⟪e, action A e⟫_ℝ ≤ β * ‖e‖ ^ 2

end KVApproximation.Tensor
