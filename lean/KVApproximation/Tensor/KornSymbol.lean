module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Fourier symbol of the symmetric gradient
-/

public section

namespace KVApproximation.Tensor

private theorem real_symmetrized_rankOne {ι : Type*} [Fintype ι]
    (a k : ι → ℝ) :
    2 * (∑ i, ∑ j, ((a i * k j + a j * k i) / 2) ^ 2) =
      (∑ i, a i ^ 2) * (∑ j, k j ^ 2) + (∑ i, a i * k i) ^ 2 := by
  have hpoint (i j : ι) :
      2 * ((a i * k j + a j * k i) / 2) ^ 2 =
        (1 / 2 : ℝ) * (a i ^ 2 * k j ^ 2) +
          (1 / 2 : ℝ) * (a j ^ 2 * k i ^ 2) + (a i * k i) * (a j * k j) := by
    ring
  have hsum := congrArg (fun f : ι → ι → ℝ => ∑ i, ∑ j, f i j)
    (funext fun i => funext fun j => hpoint i j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hsum
  nlinarith only [hsum]

/-- Section 3.1, periodic Korn argument: the exact Frobenius identity for
the ordinary symmetric part of a complex amplitude and a real frequency. -/
theorem symmetrized_rankOne_sq_norm {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (k : ι → ℝ) :
    2 * (∑ i, ∑ j, ‖(a i * (k j : ℂ) + a j * (k i : ℂ)) / 2‖ ^ 2) =
      (∑ i, ‖a i‖ ^ 2) * (∑ j, k j ^ 2) + ‖∑ i, a i * (k i : ℂ)‖ ^ 2 := by
  have hnorm (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hentry (i j : ι) :
      ‖(a i * (k j : ℂ) + a j * (k i : ℂ)) / 2‖ ^ 2 =
        (((a i).re * k j + (a j).re * k i) / 2) ^ 2 +
          (((a i).im * k j + (a j).im * k i) / 2) ^ 2 := by
    rw [hnorm]
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  simp only [hentry, hnorm, Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add,
    Finset.sum_add_distrib]
  have hr := real_symmetrized_rankOne (fun i => (a i).re) k
  have hi := real_symmetrized_rankOne (fun i => (a i).im) k
  nlinarith only [hr, hi]

/-- Section 3.1, periodic Korn argument: symmetrization loses at most a
factor two in the squared norm of a Fourier gradient. -/
theorem rankOne_sq_norm_le_symmetrized {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (k : ι → ℝ) :
    (∑ i, ∑ j, ‖a i * (k j : ℂ)‖ ^ 2) ≤
      2 * (∑ i, ∑ j, ‖(a i * (k j : ℂ) + a j * (k i : ℂ)) / 2‖ ^ 2) := by
  rw [symmetrized_rankOne_sq_norm]
  have hnorm (i j : ι) : ‖a i * (k j : ℂ)‖ ^ 2 = ‖a i‖ ^ 2 * k j ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm]
  have hsum : (∑ i, ∑ j, ‖a i‖ ^ 2 * k j ^ 2) =
      (∑ i, ‖a i‖ ^ 2) * (∑ j, k j ^ 2) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [hsum]
  exact le_add_of_nonneg_right (sq_nonneg _)

end KVApproximation.Tensor
