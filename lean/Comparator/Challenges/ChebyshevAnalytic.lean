module

public import KVApproximation.Approximation.ChebyshevCoefficients
public import KVApproximation.Approximation.Interpolation
public import Mathlib.RingTheory.Polynomial.Chebyshev

public section

namespace KVApproximation.Approximation

/-- Lemma B.9, proof: analyticity on a Bernstein ellipse gives geometric
decay of the scalar Chebyshev coefficients. -/
theorem norm_chebyshevCoefficient_le {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ))
    (hbound : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) (k : ℕ) :
    ‖chebyshevCoefficient f k‖ ≤ 2 * M / ρ ^ k := by
  sorry

/-- Lemma B.9, proof: the Chebyshev series of an analytic scalar function
converges to it throughout the closed reference interval. -/
theorem hasSum_chebyshevSeries {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ))
    (hbound : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    HasSum (fun k => chebyshevCoefficient f k *
      (((Polynomial.Chebyshev.T ℝ k).eval x : ℝ) : ℂ)) (f x) := by
  sorry

end KVApproximation.Approximation
