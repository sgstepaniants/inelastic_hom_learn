module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fourier symbol of the symmetric gradient
-/

public section

namespace KVApproximation.Tensor

/-- Section 3.1, periodic Korn argument: the exact Frobenius identity for
the ordinary symmetric part of a complex amplitude and a real frequency. -/
theorem symmetrized_rankOne_sq_norm {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (k : ι → ℝ) :
    2 * (∑ i, ∑ j, ‖(a i * (k j : ℂ) + a j * (k i : ℂ)) / 2‖ ^ 2) =
      (∑ i, ‖a i‖ ^ 2) * (∑ j, k j ^ 2) + ‖∑ i, a i * (k i : ℂ)‖ ^ 2 := by
  sorry

/-- Section 3.1, periodic Korn argument: symmetrization loses at most a
factor two in the squared norm of a Fourier gradient. -/
theorem rankOne_sq_norm_le_symmetrized {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (k : ι → ℝ) :
    (∑ i, ∑ j, ‖a i * (k j : ℂ)‖ ^ 2) ≤
      2 * (∑ i, ∑ j, ‖(a i * (k j : ℂ) + a j * (k i : ℂ)) / 2‖ ^ 2) := by
  sorry

end KVApproximation.Tensor
