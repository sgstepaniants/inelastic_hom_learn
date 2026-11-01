import KVApproximation.Approximation.PartitionResponseContinuity
import KVApproximation.Approximation.RealLocalChebyshev

/-!
# The partition preserves the local interpolation bound
-/

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Proposition B.10: nonnegative partition weights preserve the local
error constant without any factor counting patches or interpolation nodes. -/
theorem partition_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower upper t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : r ∈ Set.Icc lower upper) :
    ‖realWeightedResponse (βE / βV) e t r -
      partitionResponse (βE / βV) lower upper m e t r‖ ≤
      localResponseErrorBound δ βV m := by
  let R := logarithmicSpan lower upper
  let w := spectralWeight lower upper
  let W := realWeightedResponse (βE / βV) e t r
  let p (j : Fin (logPartitionCount R)) :=
    realLocalResponseInterpolant (βE / βV) lower R m j e t (localCoordinate lower R j r)
  have hR : 0 < R := logarithmicSpan_pos hlower horder
  have hsum : ∑ j, w j r = 1 := sum_spectralWeight hlower horder hr
  have heq : W - partitionResponse (βE / βV) lower upper m e t r =
      ∑ j, w j r • (W - p j) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
    rfl
  have hlocal (j : Fin (logPartitionCount R)) :
      ‖w j r • (W - p j)‖ ≤ w j r * localResponseErrorBound δ βV m := by
    by_cases hp : r ∈ Set.Icc (lower * Real.exp (logPatchLeft R j))
        (lower * Real.exp (logPatchRight R j))
    · have h := real_local_response_error e hβE hβV he hlower hR ht hm j
        (localCoordinate_mem hlower hR j hp)
      rw [localRate_localCoordinate hlower hR j (hlower.trans_le hr.1)] at h
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (spectralWeight_nonneg _ _ j r)]
      exact mul_le_mul_of_nonneg_left h (spectralWeight_nonneg _ _ j r)
    · have hz : w j r = 0 := spectralWeight_eq_zero_of_not_mem hlower horder j hr hp
      simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
  change ‖W - partitionResponse (βE / βV) lower upper m e t r‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ j, ‖w j r • (W - p j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, w j r * localResponseErrorBound δ βV m :=
      Finset.sum_le_sum (fun j _ => hlocal j)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

end KVApproximation.Approximation
