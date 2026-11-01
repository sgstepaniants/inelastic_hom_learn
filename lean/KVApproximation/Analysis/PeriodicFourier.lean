module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smooth Fourier monomials on the unit torus
-/

public section

noncomputable section

namespace KVApproximation.Analysis

/-- Section 3.1, periodic Sobolev foundations: the torus Fourier monomial has
the usual exponential lift with the unit-period normalization. -/
theorem mFourier_toCell {d : ℕ} (n : Fin d → ℤ) (x : EuclideanSpace ℝ (Fin d)) :
    UnitAddTorus.mFourier n (toCell x) =
      Complex.exp (∑ i, 2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ) * (x i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, toCell,
    fourier_coe_apply, Complex.ofReal_one, div_one, Complex.exp_sum]

private def fourierPhaseL {d : ℕ} (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℂ :=
  ∑ i, (2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ)) •
    (Complex.ofRealCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i))

private theorem fourierPhaseL_apply {d : ℕ} (n : Fin d → ℤ) (x : EuclideanSpace ℝ (Fin d)) :
    fourierPhaseL n x = ∑ i, 2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ) * (x i : ℂ) := by
  simp [fourierPhaseL, sum_apply, smul_apply, PiLp.proj_apply]

private theorem fourierPhaseL_basis {d : ℕ} (n : Fin d → ℤ) (j : Fin d) :
    fourierPhaseL n (WithLp.toLp 2 (Pi.single j (1 : ℝ))) =
      2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ) := by
  classical
  rw [fourierPhaseL_apply]
  simp [Pi.single_apply, apply_ite]

/-- Section 3.1, periodic Sobolev foundations: every Fourier monomial is a
smooth periodic test field. -/
theorem contDiff_mFourier_lift {d : ℕ} (n : Fin d → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => UnitAddTorus.mFourier n (toCell x)) := by
  have heq : (fun x : EuclideanSpace ℝ (Fin d) => UnitAddTorus.mFourier n (toCell x)) =
      fun x => Complex.exp (fourierPhaseL n x) := by
    funext x
    rw [mFourier_toCell, fourierPhaseL_apply]
  rw [heq]
  exact (fourierPhaseL n).contDiff.cexp

/-- Section 3.1, periodic Sobolev foundations: Fourier differentiation with
the exact `2π` factor on the unit torus. -/
theorem fderiv_mFourier_lift_apply {d : ℕ} (n : Fin d → ℤ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => UnitAddTorus.mFourier n (toCell z)) x
      (WithLp.toLp 2 (Pi.single j (1 : ℝ))) =
      (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) * UnitAddTorus.mFourier n (toCell x) := by
  have heq : (fun z : EuclideanSpace ℝ (Fin d) => UnitAddTorus.mFourier n (toCell z)) =
      fun z => Complex.exp (fourierPhaseL n z) := by
    funext z
    rw [mFourier_toCell, fourierPhaseL_apply]
  rw [heq, ((fourierPhaseL n).hasFDerivAt.cexp).fderiv,
    smul_apply, fourierPhaseL_basis, smul_eq_mul,
    mFourier_toCell, ← fourierPhaseL_apply]
  exact mul_comm _ _

end KVApproximation.Analysis
