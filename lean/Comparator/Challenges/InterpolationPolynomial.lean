module

public import KVApproximation.Approximation.Interpolation

/-!
# Polynomial degree of the root-node interpolant
-/

public section

namespace KVApproximation.Approximation

/-- Lemma B.9: the Banach-valued interpolant is a polynomial of degree
at most `m - 1`, expressed by its vector coefficients. For `m = 0` the
interpolant is zero. -/
theorem chebyshevInterpolant_degree_lt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (m : ℕ) (f : ℂ → F) :
    ∃ a : Fin m → F, ∀ x : ℝ,
      chebyshevInterpolant m f x = ∑ k : Fin m, (x : ℂ) ^ k.val • a k := by
  sorry

end KVApproximation.Approximation
