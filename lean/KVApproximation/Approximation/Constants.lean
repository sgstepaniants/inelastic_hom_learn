module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Constants for analytic interpolation

The constants in Appendix B are retained exactly. Rational bounds are used only
to certify positivity of the fixed cosine appearing in Lemma B.9.
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Approximation

/-- Lemma B.9 (`lem:uniform_prony_discretization_beta`): the imaginary semiaxis
of the Bernstein ellipse with parameter `ρ`. Its use assumes `1 < ρ`. -/
def bernsteinImaginarySemiaxis (ρ : ℝ) : ℝ :=
  (ρ - ρ⁻¹) / 2

/-- Lemma B.9 (`eq:chebyshev_interp_bound_iv`): the exact factor
`1 + sec (3 / 4)` for the local logarithmic spectral coordinate. -/
def ellipseResponseFactor : ℝ :=
  1 + (Real.cos (3 / 4 : ℝ))⁻¹

/-- Lemma B.9, proof: the generic Bernstein-ellipse interpolation bound for
`m ≥ 1` root nodes, an analytic norm bound `M`, and `1 < ρ`. -/
def chebyshevErrorBound (M ρ : ℝ) (m : ℕ) : ℝ :=
  4 * M / ((ρ - 1) * ρ ^ (m - 1))

/-- Lemma B.9 (`eq:chebyshev_interp_bound_iv`): the local interpolation bound
at ellipse parameter two. Its use assumes a positive viscosity bound. -/
def localResponseErrorBound (stressScale viscosityUpper : ℝ) (m : ℕ) : ℝ :=
  (4 * stressScale / viscosityUpper * ellipseResponseFactor) / (2 : ℝ) ^ (m - 1)

/-- Proposition B.10 (`eq:prony_homogenized_error_uniform`): the exact Prony
constant. `tensorDimension` is the dimension of the symmetric strain space. -/
def pronyConstant (tensorDimension : ℕ) (stressScale : ℝ) : ℝ :=
  8 * (tensorDimension : ℝ) * ellipseResponseFactor * stressScale

/-- Proposition B.10 (`eq:prony_homogenized_error_uniform`): the error bound
for positive interpolation order `m` in the nonsingleton case. -/
def pronyErrorBound (tensorDimension : ℕ) (stressScale : ℝ) (m : ℕ) : ℝ :=
  pronyConstant tensorDimension stressScale / (2 : ℝ) ^ (m - 1)

end KVApproximation.Approximation
