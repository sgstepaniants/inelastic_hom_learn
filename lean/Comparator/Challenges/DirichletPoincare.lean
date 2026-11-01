module

public import KVApproximation.Analysis.VectorSobolevFields

/-!
# Poincaré estimates for zero-boundary displacements
-/

public section

open MeasureTheory TopologicalSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, spatial coercivity: a domain contained in a ball of
radius R has a vector Dirichlet Poincaré bound with constant 2R. -/
theorem ZeroBoundaryH1.poincare_of_subset_ball {c : PhysicalSpace d} {R : ℝ}
    (hR : 0 ≤ R) (hΩ : (Ω : Set (PhysicalSpace d)) ⊆ Metric.ball c R)
    (u : ZeroBoundaryH1 Ω) :
    ‖VectorH1.valueL Ω u.val‖ ≤ 2 * R * ‖VectorH1.gradientL Ω u.val‖ := by
  sorry

/-- Theorem 3.1, spatial coercivity: boundedness of the domain gives one
positive Poincaré constant for all displacements and microscopic scales. -/
theorem ZeroBoundaryH1.exists_poincare_constant
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ZeroBoundaryH1 Ω,
      ‖VectorH1.valueL Ω u.val‖ ≤ C * ‖VectorH1.gradientL Ω u.val‖ := by
  sorry

end KVApproximation.Analysis
