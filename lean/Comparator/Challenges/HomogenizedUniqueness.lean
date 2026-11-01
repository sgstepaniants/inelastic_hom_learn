module

public import KVApproximation.Homogenization.WeakProblem

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogenizedUniqueness.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedUniqueness.instNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedUniqueness.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedUniqueness.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), uniqueness: the
actual homogenized weak equation and prepared initial condition have at most
one finite-horizon Sobolev solution. -/
theorem homogenized_solution_unique {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (Vhom Ehom : Elasticity d)
    (hV : PositiveDefinite Vhom) (hE : PositiveDefinite Ehom)
    (K : ℝ → Elasticity d) (hK : Continuous K)
    (g₀ : SpatialL2 Ω) (f : Forcing Ω T) (u v : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsHomogenizedSolution hT Vhom Ehom K g₀ f u)
    (hv : IsHomogenizedSolution hT Vhom Ehom K g₀ f v) : u = v := by
  sorry

end KVApproximation.Homogenization
