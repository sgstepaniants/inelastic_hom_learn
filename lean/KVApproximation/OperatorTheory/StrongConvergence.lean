module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Strong convergence with moving arguments
-/

public section

open Filter
open scoped Topology

namespace KVApproximation.OperatorTheory

/-- Lemma B.5, moving arguments: uniformly bounded strongly convergent
operators preserve convergence of their inputs. -/
theorem tendsto_apply_of_uniform_bound {F G I : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {l : Filter I}
    (T : F →L[ℝ] G) (Ts : I → F →L[ℝ] G) {C : ℝ}
    (hbound : ∀ i, ‖Ts i‖ ≤ C)
    (hT : ∀ x, Tendsto (fun i => Ts i x) l (𝓝 (T x)))
    {x : F} {xs : I → F} (hx : Tendsto xs l (𝓝 x)) :
    Tendsto (fun i => Ts i (xs i)) l (𝓝 (T x)) := by
  have h₁ := (tendsto_iff_norm_sub_tendsto_zero.1 hx).const_mul C
  have h₂ := tendsto_iff_norm_sub_tendsto_zero.1 (hT x)
  have hr : Tendsto (fun i => C * ‖xs i - x‖ + ‖Ts i x - T x‖) l (𝓝 0) := by
    simpa only [mul_zero, zero_add] using h₁.add h₂
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply tendsto_const_nhds.squeeze hr (fun i => norm_nonneg (Ts i (xs i) - T x))
  intro i
  calc
    ‖Ts i (xs i) - T x‖ = ‖Ts i (xs i - x) + (Ts i x - T x)‖ := by
      rw [map_sub, sub_add_sub_cancel]
    _ ≤ ‖Ts i (xs i - x)‖ + ‖Ts i x - T x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add_left
      (((Ts i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg _))) _

end KVApproximation.OperatorTheory
