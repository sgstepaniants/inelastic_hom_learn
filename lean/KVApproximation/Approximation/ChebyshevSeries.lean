module

public import KVApproximation.Approximation.ChebyshevNodes
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp

/-!
# Interpolation error from Chebyshev coefficient decay
-/

public section

namespace KVApproximation.Approximation

open Polynomial.Chebyshev

/-- Lemma B.9, proof: the polynomial interpolant is the finite weighted node sum. -/
private theorem interpolated_mode_eval (m k : ℕ) (x : ℝ) :
    (Lagrange.interpolate Finset.univ (chebyshevNode m)
      (fun i => (T ℝ k).eval (chebyshevNode m i))).eval x =
      ∑ i : Fin m, (chebyshevLagrange m i).eval x * (T ℝ k).eval (chebyshevNode m i) := by
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, chebyshevLagrange, mul_comm]

/-- Lemma B.9, proof: geometric coefficient decay and a Chebyshev expansion
give the paper's exact root-interpolation error constant. -/
theorem chebyshev_series_interpolation_error_le
    {f : ℂ → ℂ} {c : ℕ → ℂ} {ρ M : ℝ} {m : ℕ}
    (hρ : 1 < ρ) (hM : 0 ≤ M) (hm : 0 < m)
    (hseries : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      HasSum (fun k => c k * (((T ℝ k).eval x : ℝ) : ℂ)) (f x))
    (hcoeff : ∀ k, ‖c k‖ ≤ 2 * M / ρ ^ k)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖f x - chebyshevInterpolant m f x‖ ≤ chebyshevErrorBound M ρ m := by
  let q (k : ℕ) := Lagrange.interpolate Finset.univ (chebyshevNode m)
    (fun i => (T ℝ k).eval (chebyshevNode m i))
  let b (k : ℕ) : ℂ := c k * ((((T ℝ k).eval x : ℝ) : ℂ) - (((q k).eval x : ℝ) : ℂ))
  have hisum : HasSum (fun k => c k * (((q k).eval x : ℝ) : ℂ))
      (chebyshevInterpolant m f x) := by
    have hnode (i : Fin m) := (hseries (chebyshevNode m i) (chebyshevNode_mem m i)).mul_left
      (((chebyshevLagrange m i).eval x : ℝ) : ℂ)
    convert (hasSum_sum (s := Finset.univ) (fun i _ => hnode i)) using 1
    · ext k
      simp only [q, interpolated_mode_eval, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [chebyshevInterpolant, smul_eq_mul]
  have hb : HasSum b (f x - chebyshevInterpolant m f x) := by
    simpa only [b, mul_sub] using (hseries x hx).sub hisum
  have hzero {k : ℕ} (hk : k < m) : b k = 0 := by
    have hdegree : (T ℝ k).degree < m := by simpa [degree_T] using hk
    dsimp only [b, q]
    rw [chebyshev_interpolation_exact hdegree, sub_self, mul_zero]
  have htail : HasSum (fun k => b (k + m)) (f x - chebyshevInterpolant m f x) := by
    have hhead : ∑ k ∈ Finset.range m, b k = 0 :=
      Finset.sum_eq_zero (fun k hk => hzero (Finset.mem_range.mp hk))
    simpa only [hhead, sub_zero] using (hasSum_nat_add_iff' m).mpr hb
  have hmode (k : ℕ) :
      ‖(((T ℝ k).eval x : ℝ) : ℂ) - (((q k).eval x : ℝ) : ℂ)‖ ≤ 2 := by
    have hT := abs_eval_T_real_le_one (k : ℤ) (abs_le.mpr hx)
    have hq := chebyshev_interpolation_T_bound hm k hx
    have hn := norm_sub_le (((T ℝ k).eval x : ℝ) : ℂ) (((q k).eval x : ℝ) : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs] at hn
    exact hn.trans (by dsimp only [q]; linarith)
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  have hgeom : HasSum (fun k : ℕ => 4 * M / ρ ^ (k + m))
      (chebyshevErrorBound M ρ m) := by
    have hg := (hasSum_geometric_of_lt_one (inv_nonneg.mpr hρpos.le)
      ((inv_lt_one₀ hρpos).mpr hρ)).mul_left (4 * M / ρ ^ m)
    convert hg using 1
    · ext k
      simp only [pow_add, div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    · have hpow : ρ ^ m = ρ ^ (m - 1) * ρ := by
        conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ]
      unfold chebyshevErrorBound
      rw [hpow]
      field_simp
  apply htail.norm_le_of_bounded hgeom
  intro k
  calc
    ‖b (k + m)‖ ≤ (2 * M / ρ ^ (k + m)) * 2 := by
      dsimp only [b]
      rw [norm_mul]
      exact mul_le_mul (hcoeff _) (hmode _) (norm_nonneg _) (by positivity)
    _ = 4 * M / ρ ^ (k + m) := by ring

end KVApproximation.Approximation
