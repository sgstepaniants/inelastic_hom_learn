module

public import KVApproximation.Analysis.VectorSobolevFields
public import KVApproximation.Analysis.SobolevDirectionalDerivative

/-!
# Korn estimates for zero-boundary displacements
-/

public section

open MeasureTheory TopologicalSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, spatial coercivity: the exact strain-energy identity
on H¹₀, with the divergence formed in scalar L². -/
theorem ZeroBoundaryH1.korn_identity (u : ZeroBoundaryH1 Ω) :
    2 * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 =
      ‖VectorH1.gradientL Ω u.val‖ ^ 2 +
        ‖∑ i : Fin d, directionalDerivativeL volume Ω
          (EuclideanSpace.basisFun (Fin d) ℝ i) (u.val i)‖ ^ 2 := by
  sorry

/-- Theorem 3.1, spatial coercivity: the Dirichlet Korn inequality
has squared constant two, independently of domain and dimension. -/
theorem ZeroBoundaryH1.norm_gradientL_sq_le (u : ZeroBoundaryH1 Ω) :
    ‖VectorH1.gradientL Ω u.val‖ ^ 2 ≤
      2 * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 := by
  sorry

/-- Theorem 3.1, spatial coercivity: the full weak gradient is
bounded by √2 times the symmetric gradient. -/
theorem ZeroBoundaryH1.norm_gradientL_le (u : ZeroBoundaryH1 Ω) :
    ‖VectorH1.gradientL Ω u.val‖ ≤
      Real.sqrt 2 * ‖VectorH1.symmetricGradientL Ω u.val‖ := by
  sorry

/-- Theorem 3.1, spatial coercivity: on a bounded domain, the strain
controls the full H¹ norm with a positive constant independent of
the microscopic coefficients and their scale. -/
theorem ZeroBoundaryH1.exists_korn_constant
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ZeroBoundaryH1 Ω,
      ‖u‖ ≤ C * ‖VectorH1.symmetricGradientL Ω u.val‖ := by
  sorry

end KVApproximation.Analysis
