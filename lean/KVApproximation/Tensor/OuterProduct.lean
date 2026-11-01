module

public import KVApproximation.Tensor.Spaces
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Physical-coordinate outer products
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Theorem 3.1, localized gradient product rule: the outer product
has displacement component first and derivative direction second. -/
def outerL (d : ℕ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] SecondOrder d :=
  let B : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] SecondOrder d :=
    LinearMap.mk₂ ℝ (fun a b => WithLp.toLp 2 (fun ij => a ij.1 * b ij.2))
      (by intros; ext ij; exact add_mul _ _ _)
      (by intros; ext ij; exact mul_assoc _ _ _)
      (by intros; ext ij; exact mul_add _ _ _)
      (by intros; ext ij; exact mul_left_comm _ _ _)
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℝ (Fin d) →ₗ[ℝ] SecondOrder d) ≃ₗ[ℝ]
        (EuclideanSpace ℝ (Fin d) →L[ℝ] SecondOrder d)).toLinearMap.comp B)

end KVApproximation.Tensor
