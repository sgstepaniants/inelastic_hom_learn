module

public import KVApproximation.Approximation.ChebyshevNodes
public import Mathlib.Algebra.Polynomial.Eval.Degree

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
  refine ⟨fun k => ∑ i : Fin m, ((chebyshevLagrange m i).coeff k.val : ℂ) •
    f (chebyshevNode m i), ?_⟩
  intro x
  have heval (i : Fin m) : (((chebyshevLagrange m i).eval x : ℝ) : ℂ) =
      ∑ k : Fin m, (x : ℂ) ^ k.val * ((chebyshevLagrange m i).coeff k.val : ℂ) := by
    have hdegree : (chebyshevLagrange m i).natDegree = m - 1 := by
      simpa only [chebyshevLagrange, Finset.card_univ, Fintype.card_fin] using
        Lagrange.natDegree_basis (chebyshevNode_injective m).injOn (Finset.mem_univ i)
    have hlt : (chebyshevLagrange m i).natDegree < m := by
      rw [hdegree]
      have := i.isLt
      omega
    rw [Polynomial.eval_eq_sum_range' hlt x, ← Fin.sum_univ_eq_sum_range]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [chebyshevInterpolant, heval, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

end KVApproximation.Approximation
