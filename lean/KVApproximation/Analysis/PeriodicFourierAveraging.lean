module

public import KVApproximation.Analysis.PeriodicFourier
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Averaging of rescaled Fourier modes

The unit-torus normalization agrees with the Euclidean Fourier character.
For each nonzero lattice frequency, inverse spatial scaling sends the
physical frequency to infinity, where the Riemann–Lebesgue lemma applies.
-/

public section

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace KVApproximation.Analysis

private def latticeVector {d : ℕ} (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (n i : ℝ))

private theorem rescale_mFourier_eq {d : ℕ} (n : Fin d → ℤ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    rescalePeriodic (UnitAddTorus.mFourier n) ε x =
      (Real.fourierChar (-⟪x, (-ε⁻¹) • latticeVector n⟫) : ℂ) := by
  have hi : -⟪x, (-ε⁻¹) • latticeVector n⟫ =
      ∑ i, (n i : ℝ) * (ε⁻¹ * x i) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      PiLp.smul_apply, smul_eq_mul, latticeVector]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Real.fourierChar_apply, hi]
  simp only [rescalePeriodic, mFourier_toCell, PiLp.smul_apply, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem latticeFrequency_tendsto {d : ℕ} {n : Fin d → ℤ} (hn : n ≠ 0) :
    Tendsto (fun ε : ℝ => (-ε⁻¹) • latticeVector n) (𝓝[>] (0 : ℝ))
      (cocompact (EuclideanSpace ℝ (Fin d))) := by
  have hv : latticeVector n ≠ 0 := by
    intro heq
    apply hn
    funext i
    have hi := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) heq
    simpa [latticeVector] using hi
  have hnorm : Tendsto (fun ε : ℝ => ‖(-ε⁻¹) • latticeVector n‖)
      (𝓝[>] (0 : ℝ)) atTop := by
    have h := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).atTop_mul_const
      (norm_pos_iff.mpr hv)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  rw [← Metric.cobounded_eq_cocompact]
  exact tendsto_norm_atTop_iff_cobounded.mp hnorm

/-- Theorem 3.1, periodic weak averaging: every nonconstant rescaled
Fourier mode vanishes against a fixed spatial test as the positive scale
tends to zero; the constant mode retains the test integral. -/
theorem tendsto_integral_rescale_mFourier_mul {d : ℕ} (n : Fin d → ℤ)
    (g : EuclideanSpace ℝ (Fin d) → ℂ) :
    Tendsto (fun ε : ℝ => ∫ x, rescalePeriodic (UnitAddTorus.mFourier n) ε x * g x)
      (𝓝[>] (0 : ℝ)) (𝓝 (if n = 0 then ∫ x, g x else 0)) := by
  by_cases hn : n = 0
  · subst n
    simp [rescalePeriodic, UnitAddTorus.mFourier_zero]
  · simp only [ite_eq_right hn]
    have h := (tendsto_integral_exp_inner_smul_cocompact g).comp
      (latticeFrequency_tendsto hn)
    simpa only [Function.comp_def, Circle.smul_def, smul_eq_mul,
      ← rescale_mFourier_eq] using h

end KVApproximation.Analysis
