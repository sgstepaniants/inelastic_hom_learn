module

public import KVApproximation.Analysis.PeriodicSobolev

/-!
# Fourier tests for periodic Sobolev spaces
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Section 3.1, periodic Sobolev foundations: real weak derivatives may be
tested against a complex periodic field by its real and imaginary parts. -/
theorem HasPeriodicWeakGradient.integral_complex_test {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g : Lp (KVApproximation.Tensor.SecondOrder d) 2 (cellMeasure d)}
    (h : HasPeriodicWeakGradient u g) (φ : PeriodicC1 d ℂ) (i j : Fin d) :
    (∫ y, u y i • φ.partial j y ∂cellMeasure d) =
      -(∫ y, g y (i, j) • φ.value y ∂cellMeasure d) := by
  sorry

/-- Section 3.1, periodic Sobolev foundations: the torus Fourier monomial has
the usual exponential lift with the unit-period normalization. -/
theorem mFourier_toCell {d : ℕ} (n : Fin d → ℤ) (x : EuclideanSpace ℝ (Fin d)) :
    UnitAddTorus.mFourier n (toCell x) =
      Complex.exp (∑ i, 2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ) * (x i : ℂ)) := by
  sorry

/-- Section 3.1, periodic Sobolev foundations: every Fourier monomial is a
smooth periodic test field. -/
theorem contDiff_mFourier_lift {d : ℕ} (n : Fin d → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => UnitAddTorus.mFourier n (toCell x)) := by
  sorry

/-- Section 3.1, periodic Sobolev foundations: Fourier differentiation with
the exact `2π` factor on the unit torus. -/
theorem fderiv_mFourier_lift_apply {d : ℕ} (n : Fin d → ℤ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => UnitAddTorus.mFourier n (toCell z)) x
      (WithLp.toLp 2 (Pi.single j (1 : ℝ))) =
      (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) * UnitAddTorus.mFourier n (toCell x) := by
  sorry

/-- Section 3.1, periodic Sobolev foundations: the Fourier coefficients of
the weak gradient are frequency multiples of those of the displacement. -/
theorem HasPeriodicWeakGradient.fourier_coefficient {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g : Lp (KVApproximation.Tensor.SecondOrder d) 2 (cellMeasure d)}
    (h : HasPeriodicWeakGradient u g) (n : Fin d → ℤ) (i j : Fin d) :
    (∫ y, UnitAddTorus.mFourier (-n) y * (g y (i, j) : ℂ) ∂cellMeasure d) =
      (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
        ∫ y, UnitAddTorus.mFourier (-n) y * (u y i : ℂ) ∂cellMeasure d := by
  sorry

/-- Section 3.1, periodic Sobolev foundations: all Fourier coefficients
determine a complex L² field on the normalized unit torus. -/
theorem eq_of_fourier_integrals_eq {d : ℕ}
    {f g : Lp ℂ 2 (cellMeasure d)}
    (h : ∀ n : Fin d → ℤ,
      (∫ y, UnitAddTorus.mFourier (-n) y * f y ∂cellMeasure d) =
        ∫ y, UnitAddTorus.mFourier (-n) y * g y ∂cellMeasure d) : f = g := by
  sorry

/-- Section 3.1: the periodic distributional gradient is unique. -/
theorem HasPeriodicWeakGradient.gradient_unique {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g₁ g₂ : Lp (KVApproximation.Tensor.SecondOrder d) 2 (cellMeasure d)}
    (h₁ : HasPeriodicWeakGradient u g₁) (h₂ : HasPeriodicWeakGradient u g₂) :
    g₁ = g₂ := by
  sorry

end KVApproximation.Analysis
