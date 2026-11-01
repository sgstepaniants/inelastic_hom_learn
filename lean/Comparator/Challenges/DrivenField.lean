module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Integrability of a measurable-input vector field
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace KVApproximation.Dynamics

/-- Proposition B.13, Carathéodory measurability ingredient: a globally
Lipschitz response evaluated at an essentially bounded measurable input
and a continuous state curve is integrable on each finite interval. -/
theorem integrableOn_lipschitz_driven_field
    {V Q : Type*} [NormedAddCommGroup V] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {G : V × Q → Q} {K : ℝ≥0} (hG : LipschitzWith K G)
    {v : ℝ → V} {a b R : ℝ}
    (hv : AEStronglyMeasurable v (volume.restrict (Icc a b)))
    (hR : ∀ᵐ s ∂volume.restrict (Icc a b), ‖v s‖ ≤ R)
    {x : ℝ → Q} (hx : ContinuousOn x (Icc a b)) :
    IntegrableOn (fun s => G (v s, x s)) (Icc a b) := by
  sorry

end KVApproximation.Dynamics
