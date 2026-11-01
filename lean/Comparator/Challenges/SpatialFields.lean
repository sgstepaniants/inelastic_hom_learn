module

public import KVApproximation.Analysis.VectorSobolevFields
public import KVApproximation.Homogenization.StaticWeakProblem

/-!
# Displacement fields in the spatial weak formulation
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1 (`eq:two_scale_weak_form`): the bounded strain map agrees
almost everywhere with the strain in the actual zero-boundary weak PDE. -/
theorem symmetricGradientL_apply_ae (u : ZeroBoundaryH1 Ω) :
    ∀ᵐ x ∂volume.restrict Ω,
      VectorH1.symmetricGradientL Ω u.val x = symmetricGradient u x := by
  sorry

/-- Theorem 3.1 (`eq:two_scale_weak_form`): the actual weak strain is
square integrable, without a finite-volume assumption. -/
theorem symmetricGradient_memLp (u : ZeroBoundaryH1 Ω) :
    MemLp (symmetricGradient u) 2 (volume.restrict Ω) := by
  sorry

/-- Theorem 3.1, forcing term: the spatial load is the L² inner product
with the bounded displacement map. -/
theorem loadPairing_eq_inner (f : SpatialL2 Ω) (v : ZeroBoundaryH1 Ω) :
    loadPairing f v = ⟪f, VectorH1.valueL Ω v.val⟫_ℝ := by
  sorry

/-- Theorem 3.1, forcing term: its norm bound uses the full H¹ norm with
constant one, independently of the microscopic coefficients. -/
theorem abs_loadPairing_le (f : SpatialL2 Ω) (v : ZeroBoundaryH1 Ω) :
    |loadPairing f v| ≤ ‖f‖ * ‖v‖ := by
  sorry

end KVApproximation.Homogenization
