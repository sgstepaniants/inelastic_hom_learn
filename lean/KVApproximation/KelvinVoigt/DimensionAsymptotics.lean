module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import KVApproximation.Approximation.DimensionGrowth
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic state dimension
-/

public section

open Filter Asymptotics
open scoped Topology

namespace KVApproximation.KelvinVoigt

/-- Theorem 4.5, estimate following its proof: one dimension-dependent
constant bounds the sufficient dimension for every span and relative error. -/
theorem sufficientDimension_uniform_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R E : ℝ, 0 ≤ R → 0 < E →
      (sufficientDimension d R E : ℝ) ≤
        C * (1 + R) * (1 + max 0 (Real.log (1 / E))) := by
  obtain ⟨C, hC, hn, hbound⟩ :=
    Approximation.nonsingletonStateDimension_uniform_bound (Tensor.strainDimension d)
  refine ⟨C, hC, ?_⟩
  intro R E hR hE
  by_cases hzero : R = 0
  · subst R
    simp only [sufficientDimension, ite_true, add_zero, mul_one]
    exact hn.trans (le_mul_of_one_le_right hC.le (by linarith [le_max_left 0 (Real.log (1 / E))]))
  · simpa only [sufficientDimension, hzero, ite_false] using hbound R E hR hE

/-- Theorem 4.5 (`eq:sufficient_dimension_rates`), first limit:
logarithmic growth as relative error tends to zero from above. -/
theorem sufficientDimension_small_error (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (fun E : ℝ => (sufficientDimension d R E : ℝ)) =O[𝓝[>] 0]
      (fun E : ℝ => Real.log (1 / E)) := by
  obtain ⟨C, hC, hbound⟩ := sufficientDimension_uniform_bound d
  have hlog : Tendsto (fun E : ℝ => Real.log (1 / E)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  refine IsBigO.of_bound (2 * C * (1 + R)) ?_
  filter_upwards [eventually_mem_nhdsWithin, hlog.eventually (eventually_ge_atTop 1)]
    with E hE hlarge
  have hEpos : 0 < E := hE
  have hnonneg : 0 ≤ Real.log (1 / E) := le_trans zero_le_one hlarge
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hnonneg]
  calc
    (sufficientDimension d R E : ℝ) ≤
        C * (1 + R) * (1 + Real.log (1 / E)) := by
      simpa only [max_eq_right hnonneg] using hbound R E hR hEpos
    _ ≤ C * (1 + R) * (2 * Real.log (1 / E)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- Theorem 4.5 (`eq:sufficient_dimension_rates`), second limit:
logarithmic growth in viscosity contrast at fixed positive relative error
and fixed elasticity contrast. -/
theorem sufficientDimension_viscosity_contrast (d : ℕ) {E Celas : ℝ}
    (hE : 0 < E) (hCelas : 1 ≤ Celas) :
    (fun Cvisc : ℝ => (sufficientDimension d (Real.log (Cvisc * Celas)) E : ℝ))
      =O[atTop] (fun Cvisc : ℝ => Real.log Cvisc) := by
  obtain ⟨C, hC, hbound⟩ := sufficientDimension_uniform_bound d
  have hcpos : 0 < Celas := lt_of_lt_of_le zero_lt_one hCelas
  have hclog : 0 ≤ Real.log Celas := Real.log_nonneg hCelas
  let L := 1 + max 0 (Real.log (1 / E))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine IsBigO.of_bound (C * (2 + Real.log Celas) * L) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x hx hxlog
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxnonneg : 0 ≤ Real.log x := le_trans zero_le_one hxlog
  have hmul : Real.log (x * Celas) = Real.log x + Real.log Celas :=
    Real.log_mul hxpos.ne' hcpos.ne'
  have hR : 0 ≤ Real.log (x * Celas) := by rw [hmul]; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hxnonneg]
  have hlogbound : 1 + (Real.log x + Real.log Celas) ≤
      (2 + Real.log Celas) * Real.log x := by
    nlinarith [mul_nonneg hclog (show 0 ≤ Real.log x - 1 by linarith)]
  calc
    (sufficientDimension d (Real.log (x * Celas)) E : ℝ) ≤
        C * (1 + Real.log (x * Celas)) * L := hbound _ _ hR hE
    _ = C * (1 + (Real.log x + Real.log Celas)) * L := by rw [hmul]
    _ ≤ C * ((2 + Real.log Celas) * Real.log x) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogbound hC.le) hL
    _ = _ := by ring

/-- Theorem 4.5 (`eq:sufficient_dimension_rates`), third limit:
logarithmic growth in elasticity contrast at fixed positive relative error
and fixed viscosity contrast. -/
theorem sufficientDimension_elasticity_contrast (d : ℕ) {E Cvisc : ℝ}
    (hE : 0 < E) (hCvisc : 1 ≤ Cvisc) :
    (fun Celas : ℝ => (sufficientDimension d (Real.log (Cvisc * Celas)) E : ℝ))
      =O[atTop] (fun Celas : ℝ => Real.log Celas) := by
  simpa only [mul_comm] using
    sufficientDimension_viscosity_contrast d hE hCvisc

end KVApproximation.KelvinVoigt
