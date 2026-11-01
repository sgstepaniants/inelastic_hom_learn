module

public import KVApproximation.Approximation.Dimension

/-!
# The logarithmic mesh and interpolation order
-/

public section

namespace KVApproximation.Approximation

/-- Definition B.8: the logarithmic mesh has positive width at most one. -/
theorem logPartitionWidth_bounds {logSpan : ℝ} (hspan : 0 < logSpan) :
    0 < logPartitionWidth logSpan ∧ logPartitionWidth logSpan ≤ 1 := by
  unfold logPartitionWidth logPartitionIntervals
  have hceil : (0 : ℝ) < (⌈logSpan⌉₊ : ℝ) := hspan.trans_le (Nat.le_ceil _)
  exact ⟨div_pos hspan hceil, (div_le_one hceil).2 (Nat.le_ceil _)⟩

/-- Theorem 4.5, supporting ceiling estimate: the chosen interpolation order
makes the geometric error bound no greater than the prescribed tolerance. -/
theorem interpolationOrder_error_le {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) :
    κ / (2 : ℝ) ^ (interpolationOrder κ ε - 1) ≤ ε := by
  by_cases hzero : κ = 0
  · simp [hzero, hε.le]
  have hκpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hzero)
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : Real.log (κ / ε) / Real.log 2 ≤ (⌈log2Positive (κ / ε)⌉₊ : ℝ) :=
    (le_max_right 0 _).trans (Nat.le_ceil _)
  have hpower : κ / ε ≤ (2 : ℝ) ^ ⌈log2Positive (κ / ε)⌉₊ := by
    apply (Real.log_le_log_iff (div_pos hκpos hε) (pow_pos htwo _)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ hlogtwo).mp hceil
  have hresult : κ / (2 : ℝ) ^ ⌈log2Positive (κ / ε)⌉₊ ≤ ε := by
    apply (div_le_iff₀ (pow_pos htwo _)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hpower
  simpa only [interpolationOrder, Nat.add_comm 1, Nat.add_sub_cancel] using hresult

/-- Theorem 4.5: the chosen interpolation order has at least one node. -/
theorem interpolationOrder_pos (κ ε : ℝ) :
    0 < interpolationOrder κ ε := by
  unfold interpolationOrder
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)

end KVApproximation.Approximation
