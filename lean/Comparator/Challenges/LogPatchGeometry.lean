module

public import KVApproximation.Approximation.LogPartition

public section

namespace KVApproximation.Approximation

/-- Definition B.8: the clipped patch endpoints lie in the logarithmic interval. -/
theorem logPatch_bounds {R : ℝ} (hR : 0 < R) (j : Fin (logPartitionCount R)) :
    0 ≤ logPatchLeft R j ∧ logPatchLeft R j < logPatchRight R j ∧
      logPatchRight R j ≤ R := by
  sorry

/-- Definition B.8: each logarithmic hat is continuous. -/
theorem continuous_logHat (R : ℝ) (j : Fin (logPartitionCount R)) :
    Continuous (logHat R j) := by
  sorry

/-- Definition B.8: the partition weights are nonnegative. -/
theorem logHat_nonneg (R : ℝ) (j : Fin (logPartitionCount R)) (x : ℝ) :
    0 ≤ logHat R j x := by
  sorry

/-- Definition B.8: within the logarithmic spectral interval a hat
vanishes outside its clipped patch. -/
theorem logHat_eq_zero_of_not_mem {R : ℝ} (hR : 0 < R)
    (j : Fin (logPartitionCount R)) {x : ℝ} (hx : x ∈ Set.Icc 0 R)
    (hpatch : x ∉ Set.Icc (logPatchLeft R j) (logPatchRight R j)) :
    logHat R j x = 0 := by
  sorry

/-- Definition B.8: the exponential change of coordinates maps the
reference interval into its spectral patch. -/
theorem localRate_mem_patch {lower R : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R)) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    localRate lower R j x ∈
      Set.Icc (lower * Real.exp (logPatchLeft R j)) (lower * Real.exp (logPatchRight R j)) := by
  sorry

/-- Definition B.8: the logarithmic inverse maps each spectral patch
back into the reference interval. -/
theorem localCoordinate_mem {lower R rate : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R))
    (hrate : rate ∈ Set.Icc (lower * Real.exp (logPatchLeft R j))
      (lower * Real.exp (logPatchRight R j))) :
    localCoordinate lower R j rate ∈ Set.Icc (-1 : ℝ) 1 := by
  sorry

/-- Definition B.8: the exponential map inverts the logarithmic
coordinate at every positive rate. -/
theorem localRate_localCoordinate {lower R rate : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R)) (hrate : 0 < rate) :
    localRate lower R j (localCoordinate lower R j rate) = rate := by
  sorry

end KVApproximation.Approximation
