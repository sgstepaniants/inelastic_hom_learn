module

public import KVApproximation.Analysis.PeriodicSobolev

/-!
# Norm and average of periodic Sobolev fields
-/

public section

open MeasureTheory
open KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Section 3.1: the Sobolev norm is the Euclidean value-gradient norm. -/
theorem PeriodicH1.norm_sq {d : ℕ} (u : PeriodicH1 d) :
    ‖u‖ ^ 2 = ‖PeriodicH1.valueL d u‖ ^ 2 + ‖PeriodicH1.gradientL d u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq u,
    ← real_inner_self_eq_norm_sq (PeriodicH1.valueL d u),
    ← real_inner_self_eq_norm_sq (PeriodicH1.gradientL d u)]
  change ⟪u.val, u.val⟫_ℝ = _
  rw [L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner (𝕜 := ℝ) (PeriodicH1.valueL d u) _)
      (L2.integrable_inner (𝕜 := ℝ) (PeriodicH1.gradientL d u) _)]
  apply integral_congr_ae
  filter_upwards
    [(WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL u.val,
      (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL u.val]
      with y hv hg
  change ⟪u.val y, u.val y⟫_ℝ =
    ⟪((WithLp.fstL 2 ℝ _ _).compLpL 2 (cellMeasure d) u.val) y,
      ((WithLp.fstL 2 ℝ _ _).compLpL 2 (cellMeasure d) u.val) y⟫_ℝ +
    ⟪((WithLp.sndL 2 ℝ _ _).compLpL 2 (cellMeasure d) u.val) y,
      ((WithLp.sndL 2 ℝ _ _).compLpL 2 (cellMeasure d) u.val) y⟫_ℝ
  rw [hv, hg]
  exact WithLp.prod_inner_apply _ _

/-- Section 3.1: the constructed average is the Bochner integral on the unit cell. -/
theorem cellAverageL_eq_integral {d : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)) :
    cellAverageL d u = ∫ y, u y ∂cellMeasure d := by
  rw [cellAverageL, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (cellMeasure d) (1 : ℝ)] with y hy
  change (Lp.const 2 (cellMeasure d) (1 : ℝ)) y • u y = u y
  rw [hy]
  exact one_smul ℝ _

/-- Section 3.1: zero-mean membership uses the actual displacement integral. -/
theorem mem_zeroMeanPeriodicSubmodule_iff {d : ℕ} (u : PeriodicH1 d) :
    u ∈ zeroMeanPeriodicSubmodule d ↔
      (∫ y, PeriodicH1.valueL d u y ∂cellMeasure d) = 0 := by
  change cellAverageL d (PeriodicH1.valueL d u) = 0 ↔ _
  rw [cellAverageL_eq_integral]

end KVApproximation.Analysis
