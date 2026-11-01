module

public import KVApproximation.Analysis.PeriodicDistributionalGradient

/-!
# Periodic Sobolev bounds imply bounded variation
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Remark 4.1 (Bounded Variation): the dual variation is bounded by the
Lp norm of the actual distributional gradient for every 1 ≤ p ≤ ∞. -/
theorem periodicVariation_le_eLpNorm_gradient {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : PeriodicCell d → F} {G : PeriodicCell d → PiLp 2 (fun _ : Fin d => F)}
    {p : ENNReal} (hp : 1 ≤ p) (hG : MemLp G p (cellMeasure d))
    (hgrad : HasPeriodicDistributionalGradient A G) :
    periodicVariation A ≤ eLpNorm G p (cellMeasure d) := by
  sorry

/-- Remark 4.1 (Bounded Variation): the additive value/gradient Sobolev
bound controls the paper's L¹-plus-variation norm with constant one. -/
theorem periodicBVNorm_le_sobolevBound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : PeriodicCell d → F} {G : PeriodicCell d → PiLp 2 (fun _ : Fin d => F)}
    {p : ENNReal} (hp : 1 ≤ p) (hA : MemLp A p (cellMeasure d))
    (hG : MemLp G p (cellMeasure d)) (hgrad : HasPeriodicDistributionalGradient A G) :
    periodicBVNorm A ≤ eLpNorm A p (cellMeasure d) + eLpNorm G p (cellMeasure d) := by
  sorry

end KVApproximation.Analysis
