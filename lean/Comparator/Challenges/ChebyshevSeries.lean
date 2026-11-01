module

public import KVApproximation.Approximation.Interpolation
public import Mathlib.RingTheory.Polynomial.Chebyshev

public section

namespace KVApproximation.Approximation

/-- Lemma B.9, proof: geometric coefficient decay and a Chebyshev expansion
give the paper's exact root-interpolation error constant. -/
theorem chebyshev_series_interpolation_error_le
    {f : ℂ → ℂ} {c : ℕ → ℂ} {ρ M : ℝ} {m : ℕ}
    (hρ : 1 < ρ) (hM : 0 ≤ M) (hm : 0 < m)
    (hseries : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      HasSum (fun k => c k * (((Polynomial.Chebyshev.T ℝ k).eval x : ℝ) : ℂ)) (f x))
    (hcoeff : ∀ k, ‖c k‖ ≤ 2 * M / ρ ^ k)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖f x - chebyshevInterpolant m f x‖ ≤ chebyshevErrorBound M ρ m := by
  sorry

end KVApproximation.Approximation
