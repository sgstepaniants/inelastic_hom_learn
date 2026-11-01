module

public import KVApproximation.Approximation.LogPartitionIdentities

/-!
# Supports and inverse coordinates of logarithmic patches
-/

public section

namespace KVApproximation.Approximation

/-- Definition B.8: the clipped patch endpoints lie in the logarithmic interval. -/
theorem logPatch_bounds {R : ℝ} (hR : 0 < R) (j : Fin (logPartitionCount R)) :
    0 ≤ logPatchLeft R j ∧ logPatchLeft R j < logPatchRight R j ∧
      logPatchRight R j ≤ R := by
  exact ⟨le_max_left _ _, sub_pos.mp (logPatch_width hR j).1, min_le_left _ _⟩

/-- Definition B.8: each logarithmic hat is continuous. -/
theorem continuous_logHat (R : ℝ) (j : Fin (logPartitionCount R)) :
    Continuous (logHat R j) := by
  unfold logHat
  fun_prop

/-- Definition B.8: the partition weights are nonnegative. -/
theorem logHat_nonneg (R : ℝ) (j : Fin (logPartitionCount R)) (x : ℝ) :
    0 ≤ logHat R j x := by
  exact le_max_right _ _

/-- Definition B.8: within the logarithmic spectral interval a hat
vanishes outside its clipped patch. -/
theorem logHat_eq_zero_of_not_mem {R : ℝ} (hR : 0 < R)
    (j : Fin (logPartitionCount R)) {x : ℝ} (hx : x ∈ Set.Icc 0 R)
    (hpatch : x ∉ Set.Icc (logPatchLeft R j) (logPatchRight R j)) :
    logHat R j x = 0 := by
  have hw := (logPartitionWidth_bounds hR).1
  have habs : logPartitionWidth R ≤ |x - logPartitionCenter R j| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hpatch
    rcases hpatch with hleft | hright
    · rcases lt_max_iff.mp hleft with hxneg | hxleft
      · exact (not_lt_of_ge hx.1 hxneg).elim
      · linarith [neg_le_abs (x - logPartitionCenter R j)]
    · rcases min_lt_iff.mp hright with hxlarge | hxright
      · exact (not_lt_of_ge hx.2 hxlarge).elim
      · linarith [le_abs_self (x - logPartitionCenter R j)]
  exact max_eq_right (sub_nonpos.mpr ((one_le_div hw).mpr habs))

/-- Definition B.8: the exponential change of coordinates maps the
reference interval into its spectral patch. -/
theorem localRate_mem_patch {lower R : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R)) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    localRate lower R j x ∈
      Set.Icc (lower * Real.exp (logPatchLeft R j)) (lower * Real.exp (logPatchRight R j)) := by
  have hw : 0 ≤ (logPatchRight R j - logPatchLeft R j) / 2 :=
    (div_pos (logPatch_width hR j).1 (by norm_num)).le
  have hleft := mul_le_mul_of_nonneg_left hx.1 hw
  have hright := mul_le_mul_of_nonneg_left hx.2 hw
  constructor
  · apply mul_le_mul_of_nonneg_left _ hlower.le
    exact Real.exp_le_exp.mpr (by linarith)
  · apply mul_le_mul_of_nonneg_left _ hlower.le
    exact Real.exp_le_exp.mpr (by linarith)

/-- Definition B.8: the logarithmic inverse maps each spectral patch
back into the reference interval. -/
theorem localCoordinate_mem {lower R rate : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R))
    (hrate : rate ∈ Set.Icc (lower * Real.exp (logPatchLeft R j))
      (lower * Real.exp (logPatchRight R j))) :
    localCoordinate lower R j rate ∈ Set.Icc (-1 : ℝ) 1 := by
  have hpos : 0 < rate := (mul_pos hlower (Real.exp_pos _)).trans_le hrate.1
  have ha : logPatchLeft R j ≤ Real.log (rate / lower) := by
    apply (Real.le_log_iff_exp_le (div_pos hpos hlower)).mpr
    apply (le_div_iff₀ hlower).mpr
    simpa only [mul_comm] using hrate.1
  have hb : Real.log (rate / lower) ≤ logPatchRight R j := by
    apply (Real.log_le_iff_le_exp (div_pos hpos hlower)).mpr
    apply (div_le_iff₀ hlower).mpr
    simpa only [mul_comm] using hrate.2
  have hw := (logPatch_width hR j).1
  constructor
  · apply (le_div_iff₀ hw).mpr
    linarith
  · apply (div_le_iff₀ hw).mpr
    linarith

/-- Definition B.8: the exponential map inverts the logarithmic
coordinate at every positive rate. -/
theorem localRate_localCoordinate {lower R rate : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R)) (hrate : 0 < rate) :
    localRate lower R j (localCoordinate lower R j rate) = rate := by
  have hw := (logPatch_width hR j).1.ne'
  unfold localRate localCoordinate
  rw [show (logPatchLeft R j + logPatchRight R j) / 2 +
      (logPatchRight R j - logPatchLeft R j) / 2 *
        ((2 * Real.log (rate / lower) - logPatchLeft R j - logPatchRight R j) /
          (logPatchRight R j - logPatchLeft R j)) = Real.log (rate / lower) by
    field_simp
    ring]
  rw [Real.exp_log (div_pos hrate hlower), mul_div_cancel₀ _ hlower.ne']

end KVApproximation.Approximation
