module

public import KVApproximation.Approximation.LogPatchGeometry
public import KVApproximation.Approximation.Interpolation
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Spectral weights and logarithmic patches
-/

public section

namespace KVApproximation.Approximation

/-- Definition B.8: a nondegenerate positive interval has positive
logarithmic span. -/
theorem logarithmicSpan_pos {lower upper : ℝ}
    (hlower : 0 < lower) (horder : lower < upper) :
    0 < logarithmicSpan lower upper :=
  Real.log_pos ((one_lt_div hlower).mpr horder)

/-- Definition B.8: logarithmic rates stay in the logarithmic interval. -/
private theorem log_rate_mem {lower upper rate : ℝ}
    (hlower : 0 < lower) (hrate : rate ∈ Set.Icc lower upper) :
    Real.log (rate / lower) ∈ Set.Icc 0 (logarithmicSpan lower upper) := by
  exact ⟨Real.log_nonneg ((one_le_div hlower).mpr hrate.1),
    Real.log_le_log (div_pos (hlower.trans_le hrate.1) hlower)
      (div_le_div_of_nonneg_right hrate.2 hlower.le)⟩

/-- Definition B.8: the spectral partition weights are continuous on
the spectral interval. -/
theorem continuousOn_spectralWeight {lower upper : ℝ} (hlower : 0 < lower)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) :
    ContinuousOn (spectralWeight lower upper j) (Set.Icc lower upper) := by
  intro rate hrate
  have hlog : ContinuousAt (fun r : ℝ => Real.log (r / lower)) rate :=
    (continuousAt_id.div_const lower).log
      (div_pos (hlower.trans_le hrate.1) hlower).ne'
  exact ((continuous_logHat _ j).continuousAt.comp hlog).continuousWithinAt

/-- Definition B.8: the spectral partition weights are nonnegative. -/
theorem spectralWeight_nonneg (lower upper : ℝ)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (rate : ℝ) :
    0 ≤ spectralWeight lower upper j rate :=
  logHat_nonneg _ _ _

/-- Definition B.8: the spectral weights sum to one on the common interval. -/
theorem sum_spectralWeight {lower upper rate : ℝ}
    (hlower : 0 < lower) (horder : lower < upper)
    (hrate : rate ∈ Set.Icc lower upper) :
    ∑ j : Fin (logPartitionCount (logarithmicSpan lower upper)),
      spectralWeight lower upper j rate = 1 :=
  sum_logHat (logarithmicSpan_pos hlower horder) (log_rate_mem hlower hrate)

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
  apply logHat_eq_zero_of_not_mem (logarithmicSpan_pos hlower horder) j
    (log_rate_mem hlower hrate)
  intro hx
  apply hpatch
  have he : lower * Real.exp (Real.log (rate / lower)) = rate := by
    rw [Real.exp_log (div_pos (hlower.trans_le hrate.1) hlower),
      mul_div_cancel₀ _ hlower.ne']
  constructor
  · rw [← he]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.1) hlower.le
  · calc
      rate = lower * Real.exp (Real.log (rate / lower)) := he.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx.2) hlower.le

/-- Definition B.8: every local rate map takes the reference interval
into the common spectral interval. -/
theorem localRate_mem_interval {lower upper : ℝ}
    (hlower : 0 < lower) (horder : lower < upper)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper)))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    localRate lower (logarithmicSpan lower upper) j x ∈ Set.Icc lower upper := by
  have hR := logarithmicSpan_pos hlower horder
  have hb := logPatch_bounds hR j
  have hp := localRate_mem_patch hlower hR j hx
  constructor
  · calc
      lower = lower * Real.exp 0 := by simp
      _ ≤ lower * Real.exp (logPatchLeft (logarithmicSpan lower upper) j) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb.1) hlower.le
      _ ≤ _ := hp.1
  · calc
      _ ≤ lower * Real.exp (logPatchRight (logarithmicSpan lower upper) j) := hp.2
      _ ≤ lower * Real.exp (logarithmicSpan lower upper) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb.2.2) hlower.le
      _ = upper := by
        rw [logarithmicSpan, Real.exp_log (div_pos (hlower.trans horder) hlower),
          mul_div_cancel₀ _ hlower.ne']

/-- Definition B.8: each inverse coordinate is continuous at positive rates. -/
theorem continuousOn_localCoordinate {lower : ℝ} (hlower : 0 < lower)
    (R : ℝ) (j : Fin (logPartitionCount R)) :
    ContinuousOn (localCoordinate lower R j) (Set.Ioi 0) := by
  intro rate hrate
  have hlog : ContinuousAt (fun r : ℝ => Real.log (r / lower)) rate :=
    (continuousAt_id.div_const lower).log (div_pos hrate hlower).ne'
  exact (((continuousAt_const.mul hlog).sub continuousAt_const).sub
    continuousAt_const).div_const _ |>.continuousWithinAt

/-- Proposition B.10, coefficient-continuity proof: the signed scalar
weight integrated against the weighted measure is continuous on the interval. -/
theorem continuousOn_localPronyWeight {lower upper : ℝ} (hlower : 0 < lower)
    (m : ℕ) (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (i : Fin m) :
    ContinuousOn (fun rate => spectralWeight lower upper j rate *
      (chebyshevLagrange m i).eval
        (localCoordinate lower (logarithmicSpan lower upper) j rate))
      (Set.Icc lower upper) := by
  exact (continuousOn_spectralWeight hlower j).mul
    ((chebyshevLagrange m i).continuous.continuousOn.comp
      ((continuousOn_localCoordinate hlower _ j).mono
        (fun _ hr => hlower.trans_le hr.1)) (Set.mapsTo_univ _ _))

end KVApproximation.Approximation
