module

public import KVApproximation.Approximation.LogPartition
public import KVApproximation.Approximation.Interpolation

/-!
# Spectral weights and logarithmic patches
-/

public section

namespace KVApproximation.Approximation

/-- Definition B.8: a nondegenerate positive interval has positive
logarithmic span. -/
theorem logarithmicSpan_pos {lower upper : ℝ}
    (hlower : 0 < lower) (horder : lower < upper) :
    0 < logarithmicSpan lower upper := by
  sorry

/-- Definition B.8: the spectral partition weights are continuous on
the spectral interval. -/
theorem continuousOn_spectralWeight {lower upper : ℝ} (hlower : 0 < lower)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) :
    ContinuousOn (spectralWeight lower upper j) (Set.Icc lower upper) := by
  sorry

/-- Definition B.8: the spectral partition weights are nonnegative. -/
theorem spectralWeight_nonneg (lower upper : ℝ)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (rate : ℝ) :
    0 ≤ spectralWeight lower upper j rate := by
  sorry

/-- Definition B.8: the spectral weights sum to one on the common interval. -/
theorem sum_spectralWeight {lower upper rate : ℝ}
    (hlower : 0 < lower) (horder : lower < upper)
    (hrate : rate ∈ Set.Icc lower upper) :
    ∑ j : Fin (logPartitionCount (logarithmicSpan lower upper)),
      spectralWeight lower upper j rate = 1 := by
  sorry

/-- Definition B.8: within the common spectral interval, each weight
vanishes outside its own closed patch. -/
theorem spectralWeight_eq_zero_of_not_mem {lower upper rate : ℝ}
    (hlower : 0 < lower) (horder : lower < upper)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper)))
    (hrate : rate ∈ Set.Icc lower upper)
    (hpatch : rate ∉ Set.Icc
      (lower * Real.exp (logPatchLeft (logarithmicSpan lower upper) j))
      (lower * Real.exp (logPatchRight (logarithmicSpan lower upper) j))) :
    spectralWeight lower upper j rate = 0 := by
  sorry

/-- Definition B.8: every local rate map takes the reference interval
into the common spectral interval. -/
theorem localRate_mem_interval {lower upper : ℝ}
    (hlower : 0 < lower) (horder : lower < upper)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper)))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    localRate lower (logarithmicSpan lower upper) j x ∈ Set.Icc lower upper := by
  sorry

/-- Definition B.8: each inverse coordinate is continuous at positive rates. -/
theorem continuousOn_localCoordinate {lower : ℝ} (hlower : 0 < lower)
    (R : ℝ) (j : Fin (logPartitionCount R)) :
    ContinuousOn (localCoordinate lower R j) (Set.Ioi 0) := by
  sorry

/-- Proposition B.10, coefficient-continuity proof: the signed scalar
weight integrated against the weighted measure is continuous on the interval. -/
theorem continuousOn_localPronyWeight {lower upper : ℝ} (hlower : 0 < lower)
    (m : ℕ) (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (i : Fin m) :
    ContinuousOn (fun rate => spectralWeight lower upper j rate *
      (chebyshevLagrange m i).eval
        (localCoordinate lower (logarithmicSpan lower upper) j rate))
      (Set.Icc lower upper) := by
  sorry

end KVApproximation.Approximation
