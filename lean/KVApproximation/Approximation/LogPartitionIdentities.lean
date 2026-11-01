module

public import KVApproximation.Approximation.LogPartition
public import KVApproximation.Approximation.DimensionEstimates
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Logarithmic patches and local coordinates
-/

public section

namespace KVApproximation.Approximation

/-- Definition B.8: a unit hat is a second difference of positive parts. -/
private theorem unit_hat_difference (y : ℝ) :
    max (1 - |y|) 0 = max (y + 1) 0 - 2 * max y 0 + max (y - 1) 0 := by
  rcases le_total y 0 with hy | hy
  · rw [abs_of_nonpos hy, max_eq_right hy,
      max_eq_right (show y - 1 ≤ 0 by linarith)]
    simp only [sub_neg_eq_add, mul_zero, sub_zero, zero_add, add_comm]
  · rw [abs_of_nonneg hy, max_eq_left hy,
      max_eq_left (show 0 ≤ y + 1 by linarith)]
    rcases le_total y 1 with hy1 | hy1
    · rw [max_eq_left (show 0 ≤ 1 - y by linarith),
        max_eq_right (show y - 1 ≤ 0 by linarith)]
      ring
    · rw [max_eq_right (show 1 - y ≤ 0 by linarith),
        max_eq_left (show 0 ≤ y - 1 by linarith)]
      ring

/-- Definition B.8: the second differences telescope to the endpoint terms. -/
private theorem sum_unit_hats (n : ℕ) (y : ℝ) :
    (∑ j : Fin (n + 1), max (1 - |y - (j.val : ℝ)|) 0) =
      max (y + 1) 0 - max y 0 - max (y - n) 0 + max (y - n - 1) 0 := by
  induction n with
  | zero =>
      rw [show (0 + 1 : ℕ) = 1 by rfl, Fin.sum_univ_one]
      simpa only [Fin.val_zero, Nat.cast_zero, sub_zero, two_mul, sub_add_eq_sub_sub] using
        unit_hat_difference y
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, unit_hat_difference]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show y - ((n : ℝ) + 1) + 1 = y - n by ring,
        show y - n - 1 = y - ((n : ℝ) + 1) by ring]
      ring

/-- Definition B.8: the last grid point is the logarithmic span. -/
private theorem mesh_endpoint {R : ℝ} (hR : 0 < R) :
    (logPartitionIntervals R : ℝ) * logPartitionWidth R = R := by
  have hn : (logPartitionIntervals R : ℝ) ≠ 0 :=
    (hR.trans_le (Nat.le_ceil R)).ne'
  exact mul_div_cancel₀ R hn

/-- Definition B.8: every grid center lies in the logarithmic interval. -/
private theorem center_bounds {R : ℝ} (hR : 0 < R) (j : Fin (logPartitionCount R)) :
    0 ≤ logPartitionCenter R j ∧ logPartitionCenter R j ≤ R := by
  have hw := (logPartitionWidth_bounds hR).1.le
  have hj : j.val ≤ logPartitionIntervals R := Nat.lt_succ_iff.mp j.isLt
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) hw
  · calc
      _ ≤ (logPartitionIntervals R : ℝ) * logPartitionWidth R :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hw
      _ = R := mesh_endpoint hR

/-- Definition B.8: the logarithmic hats form a partition of unity. -/
theorem sum_logHat {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Icc 0 R) :
    ∑ j : Fin (logPartitionCount R), logHat R j x = 1 := by
  have hw := (logPartitionWidth_bounds hR).1
  have hy0 : 0 ≤ x / logPartitionWidth R := div_nonneg hx.1 hw.le
  have hyn : x / logPartitionWidth R ≤ (logPartitionIntervals R : ℝ) := by
    apply (div_le_iff₀ hw).mpr
    rw [mesh_endpoint hR]
    exact hx.2
  have hnorm (j : Fin (logPartitionCount R)) :
      |x - logPartitionCenter R j| / logPartitionWidth R =
        |x / logPartitionWidth R - (j.val : ℝ)| := by
    calc
      _ = |(x - logPartitionCenter R j) / logPartitionWidth R| := by
        rw [abs_div, abs_of_pos hw]
      _ = _ := by
        rw [sub_div, logPartitionCenter, mul_div_cancel_right₀ _ hw.ne']
  simp only [logHat, hnorm]
  change (∑ j : Fin (logPartitionIntervals R + 1),
    max (1 - |x / logPartitionWidth R - (j.val : ℝ)|) 0) = 1
  rw [sum_unit_hats]
  rw [max_eq_left (show 0 ≤ x / logPartitionWidth R + 1 by linarith),
    max_eq_left hy0, max_eq_right (sub_nonpos.mpr hyn),
    max_eq_right (show x / logPartitionWidth R - (logPartitionIntervals R : ℝ) - 1 ≤ 0 by linarith)]
  ring

/-- Definition B.8: every patch has positive length and half-width at most one. -/
theorem logPatch_width {R : ℝ} (hR : 0 < R) (j : Fin (logPartitionCount R)) :
    0 < logPatchRight R j - logPatchLeft R j ∧
      (logPatchRight R j - logPatchLeft R j) / 2 ≤ 1 := by
  have hw := logPartitionWidth_bounds hR
  have hj := center_bounds hR j
  constructor
  · apply sub_pos.mpr
    apply max_lt_iff.mpr
    constructor
    · exact lt_min hR (add_pos_of_nonneg_of_pos hj.1 hw.1)
    · exact lt_min (by linarith) (by linarith)
  · have hright : logPatchRight R j ≤ logPartitionCenter R j + logPartitionWidth R :=
      min_le_right _ _
    have hleft : logPartitionCenter R j - logPartitionWidth R ≤ logPatchLeft R j :=
      le_max_right _ _
    linarith [hw.2]

/-- Definition B.8: the local coordinate maps are inverse on the reference interval. -/
theorem localCoordinate_localRate {lower R : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R)) {x : ℝ} (_hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    localCoordinate lower R j (localRate lower R j x) = x := by
  have hwidth := (logPatch_width hR j).1.ne'
  unfold localCoordinate localRate
  rw [mul_div_cancel_left₀ _ hlower.ne', Real.log_exp]
  field_simp
  ring

end KVApproximation.Approximation
