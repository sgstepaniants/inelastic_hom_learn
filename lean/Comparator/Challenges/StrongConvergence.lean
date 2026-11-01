module

public import Mathlib.Analysis.Normed.Operator.Basic

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
  sorry

end KVApproximation.OperatorTheory
