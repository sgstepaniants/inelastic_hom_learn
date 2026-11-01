module

public import KVApproximation.Analysis.PeriodicCell

/-!
# Bounded linear Fourier coefficient maps
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Example 2.1 and Remark 4.3, Fourier ingredient: every coordinate Fourier
coefficient is a continuous real-linear functional on the actual Euclidean L² space. -/
theorem exists_periodicFourierCoefficientCLM
    {d : ℕ} {ι : Type*} [Fintype ι] (k : Fin d → ℤ) (j : ι) :
    ∃ A : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d) →L[ℝ] ℂ,
      ∀ f : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d),
        A f = ∫ y, UnitAddTorus.mFourier (-k) y * (f y j : ℂ) ∂cellMeasure d := by
  sorry

/-- Remark 4.3, separation of function inputs: all coordinate Fourier
coefficients determine the actual Euclidean L² field on the normalized cell. -/
theorem euclideanL2_eq_of_fourier_integrals_eq
    {d : ℕ} {ι : Type*} [Fintype ι]
    {f g : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d)}
    (h : ∀ k : Fin d → ℤ, ∀ j : ι,
      (∫ y, UnitAddTorus.mFourier (-k) y * (f y j : ℂ) ∂cellMeasure d) =
        ∫ y, UnitAddTorus.mFourier (-k) y * (g y j : ℂ) ∂cellMeasure d) :
    f = g := by
  sorry

end KVApproximation.Analysis
