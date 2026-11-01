module

public import KVApproximation.Approximation.AlternativeDimension
public import KVApproximation.Approximation.DimensionEstimates
public import KVApproximation.Approximation.DimensionGrowth
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Orders and growth rates for alternative Prony constructions
-/

public section

open Asymptotics Filter

namespace KVApproximation.Approximation

/-- Remark 4.6, unweighted order selection: doubling the constant leaves
half of the prescribed tolerance for the neural-response error. -/
theorem unweighted_order_error_le {U E : ℝ} (hU : 0 ≤ U) (hE : 0 < E) :
    U / (2 : ℝ) ^ (interpolationOrder (2 * U) E - 1) ≤ E / 2 := by
  have h := interpolationOrder_error_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hU) hE
  rw [mul_div_assoc] at h
  linarith

/-- Remark 4.6, global order selection: the logarithmic ceiling reaches
the prescribed tolerance. The strict analytic estimate leaves a positive margin. -/
theorem globalInterpolationOrder_error_le_of_span_pos {tensorDimension : ℕ}
    (_hn : 0 < tensorDimension) {R E : ℝ} (hR : 0 < R) (hE : 0 < E) :
    globalPronyErrorBound tensorDimension 1 R
      (globalInterpolationOrder tensorDimension R E) ≤ E := by
  have hRpos : 0 < R := hR
  have hb : 1 < 1 + 1 / R := by linarith [one_div_pos.mpr hRpos]
  have hbpos : 0 < 1 + 1 / R := zero_lt_one.trans hb
  have hlogb : 0 < Real.log (1 + 1 / R) := Real.log_pos hb
  let κ := pronyConstant tensorDimension 1 * R
  by_cases hκ : 0 < κ
  · have hceil : Real.log (κ / E) / Real.log (1 + 1 / R) ≤
        (⌈max 0 (Real.log (κ / E) / Real.log (1 + 1 / R))⌉₊ : ℝ) :=
      (le_max_right 0 _).trans (Nat.le_ceil _)
    have hpower : κ / E ≤ (1 + 1 / R) ^
        ⌈max 0 (Real.log (κ / E) / Real.log (1 + 1 / R))⌉₊ := by
      apply (Real.log_le_log_iff (div_pos hκ hE) (pow_pos hbpos _)).mp
      rw [Real.log_pow]
      exact (div_le_iff₀ hlogb).mp hceil
    have hresult : κ / (1 + 1 / R) ^
        ⌈max 0 (Real.log (κ / E) / Real.log (1 + 1 / R))⌉₊ ≤ E := by
      apply (div_le_iff₀ (pow_pos hbpos _)).mpr
      simpa only [mul_comm] using (div_le_iff₀ hE).mp hpower
    simpa only [globalPronyErrorBound, globalInterpolationOrder,
      Nat.add_comm 1, Nat.add_sub_cancel, κ] using hresult
  · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hκ)
      (pow_nonneg hbpos.le _)).trans hE.le

/-- Remark 4.6, global order selection: the logarithmic ceiling reaches
the prescribed tolerance. The strict analytic estimate leaves a positive margin. -/
theorem globalInterpolationOrder_error_le {tensorDimension : ℕ}
    (hn : 0 < tensorDimension) {R E : ℝ} (hR : 1 ≤ R) (hE : 0 < E) :
    globalPronyErrorBound tensorDimension 1 R
      (globalInterpolationOrder tensorDimension R E) ≤ E := by
  exact globalInterpolationOrder_error_le_of_span_pos hn (lt_of_lt_of_le zero_lt_one hR) hE

/-- Remark 4.6: a fixed multiplier contributes only a constant to logarithmic growth. -/
private theorem abs_log_mul_le (a : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    |Real.log (a * x)| ≤ |Real.log a| + Real.log x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx
  by_cases ha : a = 0
  · simpa only [ha, zero_mul, Real.log_zero, abs_zero, zero_add] using hxlog
  · rw [Real.log_mul ha hxpos.ne']
    simpa only [abs_of_nonneg hxlog] using abs_add_le (Real.log a) (Real.log x)

/-- Remark 4.6, first complexity estimate: unweighted local interpolation
requires at most quadratic logarithmic growth in elasticity contrast. -/
theorem unweightedDimension_asymptotic (tensorDimension : ℕ) {E Cvisc : ℝ}
    (hE : 0 < E) (hCvisc : 1 ≤ Cvisc) :
    (fun Celas : ℝ => (unweightedDimension tensorDimension
      (Real.log (Cvisc * Celas)) E Celas : ℝ)) =O[atTop]
        (fun Celas : ℝ => (Real.log Celas) ^ 2) := by
  let a := 8 * (tensorDimension : ℝ) / Real.cos (3 / 4)
  let L := 1 + max 0 (Real.log (1 / E))
  let K := 2 + (|Real.log a| + 1) / Real.log 2
  let A := 2 * (2 + Real.log Cvisc)
  let B := (K + 1 / Real.log 2) * L
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hclog : 0 ≤ Real.log Cvisc := Real.log_nonneg hCvisc
  have hcpos : 0 < Cvisc := lt_of_lt_of_le zero_lt_one hCvisc
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine IsBigO.of_bound ((tensorDimension : ℝ) * A * B) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with x hx hxlog
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxnonneg : 0 ≤ Real.log x := le_trans zero_le_one hxlog
  have hlogmul : Real.log (Cvisc * x) = Real.log Cvisc + Real.log x :=
    Real.log_mul hcpos.ne' hxpos.ne'
  have hspan : 0 ≤ Real.log (Cvisc * x) := by rw [hlogmul]; positivity
  have hcount : (logPartitionCount (Real.log (Cvisc * x)) : ℝ) ≤ A * Real.log x := by
    have h := logPartitionCount_le hspan
    rw [hlogmul] at h
    dsimp [A]
    rw [hlogmul]
    nlinarith [mul_nonneg hclog (show 0 ≤ Real.log x - 1 by linarith)]
  have hcoef : 2 * unweightedErrorConstant tensorDimension 1 x = a * x := by
    dsimp [unweightedErrorConstant, a]
    ring
  have horder : (interpolationOrder (2 * unweightedErrorConstant tensorDimension 1 x) E : ℝ)
      ≤ B * Real.log x := by
    rw [hcoef]
    calc
      (interpolationOrder (a * x) E : ℝ) ≤
          (2 + (|Real.log (a * x)| + 1) / Real.log 2) * L := interpolationOrder_le _ hE
      _ ≤ (2 + (|Real.log a| + Real.log x + 1) / Real.log 2) * L := by
        gcongr
        exact abs_log_mul_le a hx
      _ = (K + Real.log x / Real.log 2) * L := by dsimp [K]; ring
      _ ≤ ((K + 1 / Real.log 2) * Real.log x) * L := by
        apply mul_le_mul_of_nonneg_right _ hL
        have h := mul_le_mul_of_nonneg_left hxlog hK
        calc
          K + Real.log x / Real.log 2 ≤ K * Real.log x + Real.log x / Real.log 2 :=
            add_le_add (by simpa only [mul_one] using h) le_rfl
          _ = _ := by ring
      _ = B * Real.log x := by dsimp [B]; ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (sq_nonneg _)]
  simp only [unweightedDimension, Nat.cast_mul]
  calc
    (tensorDimension : ℝ) * (logPartitionCount (Real.log (Cvisc * x)) : ℝ) *
        (interpolationOrder (2 * unweightedErrorConstant tensorDimension 1 x) E : ℝ)
        ≤ (tensorDimension : ℝ) * (A * Real.log x) * (B * Real.log x) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg _)) horder
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- Remark 4.6: the reciprocal logarithmic decay rate is at most twice the span. -/
private theorem reciprocal_log_rate_le {R : ℝ} (hR : 1 ≤ R) :
    1 / Real.log (1 + 1 / R) ≤ 2 * R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hb : 1 < 1 + 1 / R := by linarith [one_div_pos.mpr hRpos]
  have hlog : 0 < Real.log (1 + 1 / R) := Real.log_pos hb
  have hlow : 1 / (R + 1) ≤ Real.log (1 + 1 / R) := by
    calc
      1 / (R + 1) = 1 - (1 + 1 / R)⁻¹ := by
        field_simp
        ring
      _ ≤ _ := Real.one_sub_inv_le_log_of_pos (zero_lt_one.trans hb)
  have hprod : 1 ≤ Real.log (1 + 1 / R) * (R + 1) :=
    (div_le_iff₀ (by positivity : 0 < R + 1)).mp hlow
  calc
    1 / Real.log (1 + 1 / R) ≤ R + 1 :=
      (div_le_iff₀ hlog).mpr (by nlinarith)
    _ ≤ 2 * R := by linarith

/-- Remark 4.6, second complexity estimate: one logarithmic interpolant
requires at most `R log R` scalar-state growth at fixed relative accuracy. -/
theorem globalPronyDimension_asymptotic (tensorDimension : ℕ) {E : ℝ} (_hE : 0 < E) :
    (fun R : ℝ => (globalPronyDimension tensorDimension R E : ℝ)) =O[atTop]
      (fun R : ℝ => R * Real.log R) := by
  let a := pronyConstant tensorDimension 1 / E
  let C := 2 + 2 * (|Real.log a| + 1)
  refine IsBigO.of_bound ((tensorDimension : ℝ) * C) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with R hR hRlog
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlognonneg : 0 ≤ Real.log R := le_trans zero_le_one hRlog
  have hb : 1 < 1 + 1 / R := by linarith [one_div_pos.mpr hRpos]
  have hlogb : 0 < Real.log (1 + 1 / R) := Real.log_pos hb
  have hnum : Real.log (pronyConstant tensorDimension 1 * R / E) ≤
      |Real.log a| + Real.log R := by
    have heq : pronyConstant tensorDimension 1 * R / E = a * R := by dsimp [a]; ring
    rw [heq]
    exact (le_abs_self _).trans (abs_log_mul_le a hR)
  have hmax : max 0 (Real.log (pronyConstant tensorDimension 1 * R / E) /
      Real.log (1 + 1 / R)) ≤ 2 * R * (|Real.log a| + Real.log R) := by
    apply max_le (by positivity)
    calc
      Real.log (pronyConstant tensorDimension 1 * R / E) / Real.log (1 + 1 / R)
          ≤ (|Real.log a| + Real.log R) / Real.log (1 + 1 / R) :=
        div_le_div_of_nonneg_right hnum hlogb.le
      _ = (|Real.log a| + Real.log R) * (1 / Real.log (1 + 1 / R)) := by ring
      _ ≤ (|Real.log a| + Real.log R) * (2 * R) :=
        mul_le_mul_of_nonneg_left (reciprocal_log_rate_le hR) (by positivity)
      _ = _ := by ring
  have hceil := Nat.ceil_lt_add_one (le_max_left 0
    (Real.log (pronyConstant tensorDimension 1 * R / E) / Real.log (1 + 1 / R)))
  have hscale : 1 ≤ R * Real.log R := by
    simpa only [one_mul] using mul_le_mul hR hRlog zero_le_one hRpos.le
  have habs : |Real.log a| + Real.log R ≤ (|Real.log a| + 1) * Real.log R := by
    nlinarith [mul_nonneg (abs_nonneg (Real.log a))
      (show 0 ≤ Real.log R - 1 by linarith)]
  have horder : (globalInterpolationOrder tensorDimension R E : ℝ) ≤ C * (R * Real.log R) := by
    calc
      (globalInterpolationOrder tensorDimension R E : ℝ) ≤
          2 + max 0 (Real.log (pronyConstant tensorDimension 1 * R / E) /
            Real.log (1 + 1 / R)) := by
        simp only [globalInterpolationOrder, Nat.cast_add, Nat.cast_one]
        linarith
      _ ≤ 2 + 2 * R * (|Real.log a| + Real.log R) := add_le_add le_rfl hmax
      _ ≤ 2 + 2 * R * ((|Real.log a| + 1) * Real.log R) := by gcongr
      _ ≤ C * (R * Real.log R) := by dsimp [C]; nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (mul_nonneg hRpos.le hlognonneg)]
  simp only [globalPronyDimension, Nat.cast_mul]
  calc
    (tensorDimension : ℝ) * (globalInterpolationOrder tensorDimension R E : ℝ)
        ≤ (tensorDimension : ℝ) * (C * (R * Real.log R)) :=
      mul_le_mul_of_nonneg_left horder (Nat.cast_nonneg _)
    _ = _ := by ring

end KVApproximation.Approximation
