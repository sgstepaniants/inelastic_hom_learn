module

public import KVApproximation.Analysis.PeriodicFourierEnergy
public import KVApproximation.Analysis.PeriodicFourierCoefficients

/-!
# Poincaré's inequality on the unit torus
-/

public section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Section 3.1, periodic Korn argument: a zero-mean periodic displacement
is controlled by its gradient. The nonsharp constant one suffices here. -/
theorem HasPeriodicWeakGradient.poincare_sq {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g : Lp (SecondOrder d) 2 (cellMeasure d)}
    (h : HasPeriodicWeakGradient u g)
    (hmean : (∫ y, u y ∂cellMeasure d) = 0) :
    ‖u‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  apply hasSum_le ?_ (hasSum_fourier_energy u) (hasSum_fourier_energy g)
  intro n
  by_cases hn : n = 0
  · have hz (i : Fin d) : (∫ y, (u y i : ℂ) ∂cellMeasure d) = 0 := by
      let L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℂ :=
        Complex.ofRealCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i)
      change (∫ y, L (u y) ∂cellMeasure d) = 0
      rw [L.integral_comp_comm (MemLp.integrable (by norm_num) (Lp.memLp u)),
        hmean, map_zero]
    simp only [hn, neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply,
      one_mul, hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hn
    have hj' : n j ≠ 0 := hj
    have habs : (1 : ℝ) ≤ |(n j : ℝ)| := by exact_mod_cast Int.one_le_abs hj'
    have hmult : 1 ≤ ‖2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)‖ := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
        ← Complex.ofReal_intCast]
      nlinarith only [Real.two_le_pi, habs, mul_nonneg (Real.pi_pos.le)
        (sub_nonneg.mpr habs)]
    calc
      _ ≤ ∑ i, ‖∫ y, UnitAddTorus.mFourier (-n) y * (g y (i, j) : ℂ)
          ∂cellMeasure d‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [h.fourier_coefficient n i j, norm_mul, mul_pow]
        have hsq : 1 ≤ ‖2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)‖ ^ 2 := by
          nlinarith only [hmult]
        exact le_mul_of_one_le_left (sq_nonneg _) hsq
      _ ≤ _ := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_le_sum
        intro i _
        exact Finset.single_le_sum
          (f := fun k : Fin d => ‖∫ y, UnitAddTorus.mFourier (-n) y *
            (g y (i, k) : ℂ) ∂cellMeasure d‖ ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ j)

end KVApproximation.Analysis
