module

public import KVApproximation.Analysis.PeriodicFourierMode
public import KVApproximation.Analysis.PeriodicSobolev

/-!
# Smooth real Fourier synthesis statements
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Section 3.1, smooth density argument: every real Fourier mode has a
smooth periodic Euclidean lift. -/
theorem contDiff_realFourierMode_lift {d : ℕ} {ι : Type*} [Fintype ι]
    (n : Fin d → ℤ) (a : ι → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => realFourierMode n a (toCell x)) := by
  sorry

/-- Section 3.1, smooth density argument: the coordinate derivative of a
real Fourier mode retains the exact unit-torus multiplier. -/
theorem fderiv_realFourierMode_lift_apply {d : ℕ} {ι : Type*} [Fintype ι]
    (n : Fin d → ℤ) (a : ι → ℂ) (x : EuclideanSpace ℝ (Fin d))
    (i : ι) (j : Fin d) :
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => realFourierMode n a (toCell z)) x
      (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) i =
      (a i * (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
        UnitAddTorus.mFourier n (toCell x)).re := by
  sorry

/-- Section 3.1, smooth density argument: real parts of the complex Fourier
series converge in the actual Euclidean L² norm. -/
theorem hasSum_realFourier_series {d : ℕ} {ι : Type*} [Fintype ι]
    (f : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d)) :
    HasSum (fun n : Fin d → ℤ =>
      (realFourierMode n (fun i =>
        ∫ y, UnitAddTorus.mFourier (-n) y * (f y i : ℂ) ∂cellMeasure d)).toLp
        2 (cellMeasure d) ℝ) f := by
  sorry

end KVApproximation.Analysis
