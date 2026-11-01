module

public import KVApproximation.Analysis.PeriodicDivergence
public import KVApproximation.Analysis.PeriodicFourier
public import KVApproximation.Analysis.PeriodicSmoothIdentities
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Fourier coefficients of divergence-free periodic fields

Real and imaginary scalar tests give the complex distributional identity.
Testing a Fourier character then removes the common nonzero multiplier.
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

private theorem integral_complex_test {d : ℕ}
    {q : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    (h : HasPeriodicZeroDivergence q) (φ : PeriodicC1 d ℂ) :
    (∫ y, ∑ j, q y j • φ.partial j y ∂cellMeasure d) = 0 := by
  have hi (j : Fin d) : Integrable (fun y => q y j • φ.partial j y) (cellMeasure d) := by
    have hp : MemLp (φ.partial j) 2 (cellMeasure d) :=
      (φ.continuous_partial j).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact memLp_one_iff_integrable.mp (((Lp.memLp q).eval_piLp j).smul hp)
  have htest (L : ℂ →L[ℝ] ℝ) :
      L (∫ y, ∑ j, q y j • φ.partial j y ∂cellMeasure d) = 0 := by
    let ψ : PeriodicC1 d ℝ :=
      ⟨fun y => L (φ.value y), L.contDiff.comp φ.contDiff_lift⟩
    have hpartial (j : Fin d) (y : PeriodicCell d) :
        ψ.partial j y = L (φ.partial j y) := by
      have hd := L.hasFDerivAt.comp (cellRepresentative y)
        (φ.contDiff_lift.differentiable one_ne_zero (cellRepresentative y)).hasFDerivAt
      simp only [Function.comp_def] at hd
      change fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => L (φ.value (toCell x)))
        (cellRepresentative y) (WithLp.toLp 2 (Pi.single j (1 : ℝ))) = _
      rw [hd.fderiv]
      rfl
    rw [← L.integral_comp_comm (integrable_finsetSum _ (fun j _ => hi j))]
    simp only [map_sum, map_smul, smul_eq_mul]
    simpa only [hpartial] using h ψ
  apply Complex.ext
  · exact htest Complex.reCLM
  · exact htest Complex.imCLM

/-- Theorem 3.1, static flux tests: the Fourier coefficient of a
divergence-free periodic field is orthogonal to its lattice frequency. -/
theorem HasPeriodicZeroDivergence.fourier_coefficient {d : ℕ}
    {q : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    (h : HasPeriodicZeroDivergence q) (n : Fin d → ℤ) :
    (∑ j, (n j : ℂ) *
      ∫ y, UnitAddTorus.mFourier (-n) y * (q y j : ℂ) ∂cellMeasure d) = 0 := by
  let φ : PeriodicC1 d ℂ :=
    ⟨UnitAddTorus.mFourier (-n), (contDiff_mFourier_lift (-n)).of_le (by simp)⟩
  have hp (j : Fin d) (y : PeriodicCell d) :
      φ.partial j y = -(2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
        UnitAddTorus.mFourier (-n) y := by
    have hd := fderiv_mFourier_lift_apply (-n) (cellRepresentative y) j
    simpa only [φ, PeriodicC1.partial, toCell_cellRepresentative,
      Pi.neg_apply, Int.cast_neg, mul_neg] using hd
  have ht := integral_complex_test h φ
  have heq : (fun y => ∑ j, q y j • φ.partial j y) =
      fun y => -(2 * (Real.pi : ℂ) * Complex.I) *
        ∑ j, (n j : ℂ) * (UnitAddTorus.mFourier (-n) y * (q y j : ℂ)) := by
    funext y
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hp, Complex.real_smul]
    ring
  have hi (j : Fin d) : Integrable (fun y =>
      (n j : ℂ) * (UnitAddTorus.mFourier (-n) y * (q y j : ℂ))) (cellMeasure d) := by
    have hm : MemLp (UnitAddTorus.mFourier (-n)) 2 (cellMeasure d) :=
      (UnitAddTorus.mFourier (-n)).continuous.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact (memLp_one_iff_integrable.mp
      (hm.mul (((Lp.memLp q).eval_piLp j).ofReal))).const_mul _
  rw [heq, integral_const_mul, integral_finsetSum _ (fun j _ => hi j)] at ht
  simp_rw [integral_const_mul] at ht
  exact (mul_eq_zero.mp ht).resolve_left (by simp [Real.pi_ne_zero])

end KVApproximation.Analysis
