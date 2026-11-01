module

public import KVApproximation.Approximation.AlternativeProny
public import KVApproximation.KelvinVoigt.PronyProblem
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Accuracy and complexity of alternative Prony constructions
-/

public section

open Asymptotics Filter
open KVApproximation.Tensor KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hVorder hEorder

/-- Remark 4.6: the unweighted local construction has the stated elasticity-
contrast dependence. The bound retains the explicit constant from the proof. -/
theorem unweighted_prony_error_le (hδ : 0 < δ)
    (hspan : αE / βV < βE / αV) {m : ℕ} (hm : 0 < m) :
    uniformPronyError C
      (unweightedLocalModel S.measure (fun M => (C M).viscosity)
        (fun M => (C M).elasticity) (αE / βV) (βE / αV) m) δ ≤
      ENNReal.ofReal (unweightedErrorConstant (strainDimension d) δ (βE / αE) /
        (2 : ℝ) ^ (m - 1)) := by
  sorry

/-- Remark 4.6: one weighted interpolant on the full logarithmic interval
has error of order `R * (1 + 1/R)^(-(n-1))` for `R ≥ 1`. -/
theorem global_prony_error_lt (hd : 0 < d) (hδ : 0 < δ)
    (hspan : 1 ≤ logarithmicSpan (αE / βV) (βE / αV)) {n : ℕ} (hn : 0 < n) :
    uniformPronyError C
      (globalPronyModel S.measure (fun M => (C M).viscosity)
        (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) n) δ <
      ENNReal.ofReal (globalPronyErrorBound (strainDimension d) δ
        (logarithmicSpan (αE / βV) (βE / αV)) n) := by
  sorry

end KVApproximation.KelvinVoigt

namespace KVApproximation.Approximation

/-- Remark 4.6, unweighted order selection: doubling the constant leaves
half of the prescribed tolerance for the neural-response error. -/
theorem unweighted_order_error_le {U E : ℝ} (hU : 0 ≤ U) (hE : 0 < E) :
    U / (2 : ℝ) ^ (interpolationOrder (2 * U) E - 1) ≤ E / 2 := by
  sorry

/-- Remark 4.6, global order selection: the logarithmic ceiling reaches
the prescribed tolerance. The strict analytic estimate leaves a positive margin. -/
theorem globalInterpolationOrder_error_le {tensorDimension : ℕ}
    (hn : 0 < tensorDimension) {R E : ℝ} (hR : 1 ≤ R) (hE : 0 < E) :
    globalPronyErrorBound tensorDimension 1 R
      (globalInterpolationOrder tensorDimension R E) ≤ E := by
  sorry

/-- Remark 4.6, first complexity estimate: unweighted local interpolation
requires at most quadratic logarithmic growth in elasticity contrast. -/
theorem unweightedDimension_asymptotic (tensorDimension : ℕ) {E Cvisc : ℝ}
    (hE : 0 < E) (hCvisc : 1 ≤ Cvisc) :
    (fun Celas : ℝ => (unweightedDimension tensorDimension
      (Real.log (Cvisc * Celas)) E Celas : ℝ)) =O[atTop]
        (fun Celas : ℝ => (Real.log Celas) ^ 2) := by
  sorry

/-- Remark 4.6, second complexity estimate: one logarithmic interpolant
requires at most `R log R` scalar-state growth at fixed relative accuracy. -/
theorem globalPronyDimension_asymptotic (tensorDimension : ℕ) {E : ℝ} (hE : 0 < E) :
    (fun R : ℝ => (globalPronyDimension tensorDimension R E : ℝ)) =O[atTop]
      (fun R : ℝ => R * Real.log R) := by
  sorry

end KVApproximation.Approximation
