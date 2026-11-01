module

public import KVApproximation.Approximation.Dimension

/-!
# Ceiling bounds for the logarithmic construction
-/

public section

namespace KVApproximation.Approximation

/-- Theorem 4.5, asymptotic estimate: the logarithmic partition count is linear
in the span, including span zero as an algebraic boundary case. -/
theorem logPartitionCount_le {R : ℝ} (hR : 0 ≤ R) :
    (logPartitionCount R : ℝ) ≤ 2 * (1 + R) := by
  have h := Nat.ceil_lt_add_one hR
  simp only [logPartitionCount, logPartitionIntervals, Nat.cast_add, Nat.cast_one]
  linarith

/-- Theorem 4.5, asymptotic estimate: a fixed interpolation constant contributes
only a multiplicative constant to logarithmic tolerance growth. -/
theorem interpolationOrder_le (κ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (interpolationOrder κ ε : ℝ) ≤
      (2 + (|Real.log κ| + 1) / Real.log 2) *
        (1 + max 0 (Real.log (1 / ε))) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let L := max 0 (Real.log (1 / ε))
  have hL : 0 ≤ L := le_max_left _ _
  have hquot : Real.log (κ / ε) ≤ |Real.log κ| + L := by
    by_cases hκ : κ = 0
    · simp only [hκ, zero_div, Real.log_zero, abs_zero, zero_add]
      exact hL
    · rw [Real.log_div hκ hε.ne']
      have h := add_le_add (le_abs_self (Real.log κ)) (le_max_right 0 (Real.log (1 / ε)))
      simpa only [L, one_div, Real.log_inv, sub_eq_add_neg] using h
  have hlog : log2Positive (κ / ε) ≤ (|Real.log κ| + L) / Real.log 2 := by
    exact max_le (div_nonneg (add_nonneg (abs_nonneg _) hL) htwo.le)
      (div_le_div_of_nonneg_right hquot htwo.le)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ log2Positive (κ / ε) from le_max_left _ _)
  have hnum : |Real.log κ| + L ≤ (|Real.log κ| + 1) * (1 + L) := by
    nlinarith [mul_nonneg (abs_nonneg (Real.log κ)) hL]
  calc
    (interpolationOrder κ ε : ℝ) ≤ 2 + log2Positive (κ / ε) := by
      simp only [interpolationOrder, Nat.cast_add, Nat.cast_one]
      linarith
    _ ≤ 2 + (|Real.log κ| + L) / Real.log 2 := add_le_add le_rfl hlog
    _ ≤ 2 * (1 + L) + (|Real.log κ| + 1) * (1 + L) / Real.log 2 :=
      add_le_add (by nlinarith) (div_le_div_of_nonneg_right hnum htwo.le)
    _ = _ := by ring

/-- Theorem 4.5, asymptotic estimate: the nonsingleton formula has a uniform
constant depending only on the tensor dimension. -/
theorem nonsingletonStateDimension_uniform_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ (n : ℝ) ≤ C ∧ ∀ R E : ℝ, 0 ≤ R → 0 < E →
      (nonsingletonStateDimension n R E : ℝ) ≤
        C * (1 + R) * (1 + max 0 (Real.log (1 / E))) := by
  let K := 2 + (|Real.log (pronyConstant n 1)| + 1) / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 2 ≤ K := by
    exact le_add_of_nonneg_right (div_nonneg (by positivity) htwo.le)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨2 * (n + 1) * K, by positivity, by nlinarith, ?_⟩
  intro R E hR hE
  have hL : 0 ≤ max 0 (Real.log (1 / E)) := le_max_left _ _
  have hcount := logPartitionCount_le hR
  have horder := interpolationOrder_le (pronyConstant n 1) hE
  change (interpolationOrder (pronyConstant n 1) E : ℝ) ≤
    K * (1 + max 0 (Real.log (1 / E))) at horder
  simp only [nonsingletonStateDimension, Nat.cast_mul]
  calc
    (n : ℝ) * (logPartitionCount R : ℝ) * (interpolationOrder (pronyConstant n 1) E : ℝ)
        ≤ (n : ℝ) * (2 * (1 + R)) * (K * (1 + max 0 (Real.log (1 / E)))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcount hn) horder
        (Nat.cast_nonneg _) (by positivity)
    _ ≤ (n + 1) * (2 * (1 + R)) * (K * (1 + max 0 (Real.log (1 / E)))) := by
      gcongr
      linarith
    _ = _ := by ring

end KVApproximation.Approximation
