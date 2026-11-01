module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Complexity bounds for the sufficient state dimension
-/

public section

open Filter Asymptotics
open scoped Topology

namespace KVApproximation.KelvinVoigt

/-- Theorem 4.5, estimate following its proof: one dimension-dependent
constant bounds the sufficient dimension for every span and relative error. -/
theorem sufficientDimension_uniform_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R E : ℝ, 0 ≤ R → 0 < E →
      (sufficientDimension d R E : ℝ) ≤
        C * (1 + R) * (1 + max 0 (Real.log (1 / E))) := by
  sorry

/-- Theorem 4.5 (`eq:sufficient_dimension_rates`), first limit:
logarithmic growth as relative error tends to zero from above. -/
theorem sufficientDimension_small_error (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (fun E : ℝ => (sufficientDimension d R E : ℝ)) =O[𝓝[>] 0]
      (fun E : ℝ => Real.log (1 / E)) := by
  sorry

/-- Theorem 4.5 (`eq:sufficient_dimension_rates`), second limit:
logarithmic growth in viscosity contrast at fixed positive relative error
and fixed elasticity contrast. -/
theorem sufficientDimension_viscosity_contrast (d : ℕ) {E Celas : ℝ}
    (hE : 0 < E) (hCelas : 1 ≤ Celas) :
    (fun Cvisc : ℝ => (sufficientDimension d (Real.log (Cvisc * Celas)) E : ℝ))
      =O[atTop] (fun Cvisc : ℝ => Real.log Cvisc) := by
  sorry

/-- Theorem 4.5 (`eq:sufficient_dimension_rates`), third limit:
logarithmic growth in elasticity contrast at fixed positive relative error
and fixed viscosity contrast. -/
theorem sufficientDimension_elasticity_contrast (d : ℕ) {E Cvisc : ℝ}
    (hE : 0 < E) (hCvisc : 1 ≤ Cvisc) :
    (fun Celas : ℝ => (sufficientDimension d (Real.log (Cvisc * Celas)) E : ℝ))
      =O[atTop] (fun Celas : ℝ => Real.log Celas) := by
  sorry

end KVApproximation.KelvinVoigt
