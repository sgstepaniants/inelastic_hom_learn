module

public import KVApproximation.Approximation.Constants
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Analytic.Basic

/-!
# Root-node interpolation on Bernstein ellipses
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Approximation

/-- Lemma B.9, proof: the closed, filled Bernstein ellipse. Its analytic
uses assume `1 < ρ`. -/
def bernsteinEllipse (ρ : ℝ) : Set ℂ :=
  {z | (z.re / ((ρ + ρ⁻¹) / 2)) ^ 2 +
    (z.im / bernsteinImaginarySemiaxis ρ) ^ 2 ≤ 1}

/-- Definition B.8 (`def:prony_series_approximation`): the roots of `Tₘ`,
with Lean index `i` corresponding to paper index `i + 1`. -/
def chebyshevNode (m : ℕ) (i : Fin m) : ℝ :=
  Real.cos ((2 * (i.val : ℝ) + 1) * Real.pi / (2 * (m : ℝ)))

/-- Definition B.8: the Lagrange basis polynomial at a Chebyshev root. -/
def chebyshevLagrange (m : ℕ) (i : Fin m) : Polynomial ℝ :=
  Lagrange.basis Finset.univ (chebyshevNode m) i

/-- Lemma B.9, proof: interpolation of a complex Banach-space-valued
function at the `m` real Chebyshev roots. -/
def chebyshevInterpolant {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (m : ℕ) (f : ℂ → F) (x : ℝ) : F :=
  ∑ i : Fin m, (((chebyshevLagrange m i).eval x : ℝ) : ℂ) • f (chebyshevNode m i)

end KVApproximation.Approximation
