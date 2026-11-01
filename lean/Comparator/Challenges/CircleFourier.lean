module

public import KVApproximation.Analysis.AnnulusCoefficients
public import Mathlib.Analysis.Fourier.AddCircle

public section

namespace KVApproximation.Analysis

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Lemma B.9, analytic coefficient proof: the unit-radius Laurent
coefficient is the corresponding Fourier coefficient of the circle pullback. -/
theorem circleCoefficient_eq_fourierCoeff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (k : ℕ) :
    circleCoefficient f 1 k = fourierCoeff
      (fun t : AddCircle (2 * Real.pi) => f (t.toCircle : ℂ)) (k : ℤ) := by
  sorry

/-- Lemma B.9, analytic coefficient proof: an even circle function has
equal opposite Fourier coefficients, also for complex-valued functions. -/
theorem fourierCoeff_neg_of_even
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : ℝ} [Fact (0 < T)] {f : AddCircle T → F}
    (hf : ∀ t, f (-t) = f t) (k : ℤ) :
    fourierCoeff f (-k) = fourierCoeff f k := by
  sorry

end KVApproximation.Analysis
