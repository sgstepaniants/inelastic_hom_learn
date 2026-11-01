module

public import KVApproximation.Analysis.AnnulusCoefficients

public section

namespace KVApproximation.Analysis

/-- Lemma B.9, analytic coefficient proof: holomorphy on a closed annulus
makes each nonnegative Laurent coefficient independent of radius. -/
theorem circleCoefficient_eq_of_analyticOnNhd
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R \ Metric.ball 0 r)) (k : ℕ) :
    circleCoefficient f R k = circleCoefficient f r k := by
  sorry

/-- Lemma B.9, analytic coefficient proof: the circle coefficient has
the sharp geometric bound `M / R^k`. -/
theorem norm_circleCoefficient_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖circleCoefficient f R k‖ ≤ M / R ^ k := by
  sorry

end KVApproximation.Analysis
