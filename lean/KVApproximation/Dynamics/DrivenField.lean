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
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  refine (integrable_const ((K : ℝ) * max R C + ‖G (0, 0)‖)).mono'
    (hG.continuous.comp_aestronglyMeasurable
      (hv.prodMk (hx.aestronglyMeasurable measurableSet_Icc))) ?_
  filter_upwards [hR, ae_restrict_mem measurableSet_Icc] with s hs hsmem
  calc
    ‖G (v s, x s)‖ ≤ ‖G (v s, x s) - G (0, 0)‖ + ‖G (0, 0)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ (K : ℝ) * max ‖v s‖ ‖x s‖ + ‖G (0, 0)‖ := by
      gcongr
      simpa only [dist_eq_norm, Prod.norm_def, Prod.mk_sub_mk, sub_zero] using
        hG.dist_le_mul (v s, x s) (0, 0)
    _ ≤ (K : ℝ) * max R C + ‖G (0, 0)‖ := by
      gcongr
      exact hC s hsmem

end KVApproximation.Dynamics
