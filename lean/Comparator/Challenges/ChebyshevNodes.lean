module

public import KVApproximation.Approximation.Interpolation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

public section

namespace KVApproximation.Approximation

/-- Definition B.8: every root node lies in the reference interval. -/
theorem chebyshevNode_mem (m : ℕ) (i : Fin m) :
    chebyshevNode m i ∈ Set.Icc (-1 : ℝ) 1 := by
  sorry

/-- Definition B.8: the root nodes are pairwise distinct. -/
theorem chebyshevNode_injective (m : ℕ) :
    Function.Injective (chebyshevNode m) := by
  sorry

/-- Definition B.8: the interpolation nodes are roots of `Tₘ`. -/
theorem chebyshevNode_isRoot (m : ℕ) (i : Fin m) :
    (Polynomial.Chebyshev.T ℝ m).eval (chebyshevNode m i) = 0 := by
  sorry

/-- Lemma B.9, proof: root-node interpolation is exact below degree `m`. -/
theorem chebyshev_interpolation_exact {m : ℕ} {p : Polynomial ℝ}
    (hp : p.degree < m) :
    Lagrange.interpolate Finset.univ (chebyshevNode m)
      (fun i => p.eval (chebyshevNode m i)) = p := by
  sorry

/-- Lemma B.9, proof: at the roots of `Tₘ`, every Chebyshev polynomial
agrees with zero or a signed Chebyshev polynomial of degree below `m`. -/
theorem chebyshev_root_alias {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∃ p : Polynomial ℝ,
      (∀ i : Fin m, p.eval (chebyshevNode m i) =
        (Polynomial.Chebyshev.T ℝ k).eval (chebyshevNode m i)) ∧
      (p = 0 ∨ ∃ r : ℕ, r < m ∧
        (p = Polynomial.Chebyshev.T ℝ r ∨ p = -Polynomial.Chebyshev.T ℝ r)) := by
  sorry

/-- Lemma B.9, proof: interpolating a Chebyshev polynomial at the roots
of `Tₘ` has uniform norm at most one on the reference interval. -/
theorem chebyshev_interpolation_T_bound {m : ℕ} (hm : 0 < m) (k : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Lagrange.interpolate Finset.univ (chebyshevNode m)
      (fun i => (Polynomial.Chebyshev.T ℝ k).eval (chebyshevNode m i))).eval x| ≤ 1 := by
  sorry

end KVApproximation.Approximation
