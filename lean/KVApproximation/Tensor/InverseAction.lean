module

public import KVApproximation.Tensor.LinearActionIdentities
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Inverse coefficient action
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.Tensor

/-- Section 3.2 (`eq:operator_L`): a coercive elasticity tensor acts
invertibly on the finite-dimensional symmetric strain space. -/
theorem HasBounds.action_isInvertible {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 < α) (hA : HasBounds α β A) :
    (actionL d A).IsInvertible := by
  have hzero (v : Symmetric d) (hv : actionL d A v = 0) : v = 0 := by
    apply norm_eq_zero.mp
    have h := (hA v).1
    rw [← actionL_apply, hv, inner_zero_right] at h
    have hs : ‖v‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hα).mp (by simpa using h)
    exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg ‖v‖))
  have hinj : Function.Injective (actionL d A) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hzero
    simp only [map_sub, huv, sub_self]
  have hsurj : Function.Surjective (actionL d A) :=
    LinearMap.injective_iff_surjective (f := (actionL d A).toLinearMap) |>.mp hinj
  exact ⟨(LinearEquiv.ofBijective (actionL d A).toLinearMap
    ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩

/-- Section 3.2 (`eq:operator_L`): the pointwise inverse has the
reciprocal coercivity bound in the Frobenius norm. -/
theorem HasBounds.inverse_action_norm_le {d : ℕ} {α β : ℝ} {A : Elasticity d}
    (hα : 0 < α) (hA : HasBounds α β A) (v : Symmetric d) :
    ‖(actionL d A).inverse v‖ ≤ ‖v‖ / α := by
  let w := (actionL d A).inverse v
  have hw : action A w = v := (hA.action_isInvertible hα).self_apply_inverse v
  have henergy : α * ‖w‖ ^ 2 ≤ ‖w‖ * ‖v‖ := by
    have h := (hA w).1
    rw [hw] at h
    exact h.trans (real_inner_le_norm w v)
  change ‖w‖ ≤ ‖v‖ / α
  apply (le_div_iff₀ hα).2
  by_cases hz : ‖w‖ = 0
  · simp [hz]
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hz)
    have h : ‖w‖ * (‖w‖ * α) ≤ ‖w‖ * ‖v‖ := by nlinarith [henergy]
    exact (mul_le_mul_iff_right₀ hpos).mp h

end KVApproximation.Tensor
