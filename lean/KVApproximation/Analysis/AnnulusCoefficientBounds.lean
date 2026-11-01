module

public import KVApproximation.Analysis.AnnulusCoefficients
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic.FieldSimp

/-!
# Radius invariance and geometric decay of Laurent coefficients
-/

public section

namespace KVApproximation.Analysis

/-- Lemma B.9, analytic coefficient proof: holomorphy on a closed annulus
makes each nonnegative Laurent coefficient independent of radius. -/
theorem circleCoefficient_eq_of_analyticOnNhd
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R \ Metric.ball 0 r)) (k : ℕ) :
    circleCoefficient f R k = circleCoefficient f r k := by
  have hnonzero (z : ℂ) (hz : z ∈ Metric.closedBall 0 R \ Metric.ball 0 r) : z ≠ 0 := by
    intro heq
    subst z
    exact hz.2 (by simpa only [Metric.mem_ball, dist_self] using hr)
  have hd (z : ℂ) (hz : z ∈ Metric.closedBall 0 R \ Metric.ball 0 r) :
      DifferentiableAt ℂ (fun w => (w ^ (k + 1))⁻¹ • f w) z :=
    ((differentiableAt_id.pow (k + 1)).inv (pow_ne_zero _ (hnonzero z hz))).smul
      (hf z hz).differentiableAt
  unfold circleCoefficient
  congr 1
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR Set.countable_empty
  · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
  · intro z hz
    exact hd z ⟨Metric.ball_subset_closedBall hz.1.1,
      fun h => hz.1.2 (Metric.ball_subset_closedBall h)⟩

/-- Lemma B.9, analytic coefficient proof: the circle coefficient has
the sharp geometric bound `M / R^k`. -/
theorem norm_circleCoefficient_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M) (k : ℕ) :
    ‖circleCoefficient f R k‖ ≤ M / R ^ k := by
  have hi (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) R) :
      ‖(z ^ (k + 1))⁻¹ • f z‖ ≤ M / R ^ (k + 1) := by
    have hnorm : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_smul, norm_inv, norm_pow, hnorm, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hbound z hz) (inv_nonneg.mpr (pow_nonneg hR.le _))
  calc
    ‖circleCoefficient f R k‖ ≤ R * (M / R ^ (k + 1)) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hi
    _ = M / R ^ k := by rw [pow_succ]; field_simp

end KVApproximation.Analysis
