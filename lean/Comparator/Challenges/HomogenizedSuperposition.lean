module

public import KVApproximation.Homogenization.WeakProblem

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

-- Use the same named norm structures in the independent interface.
local instance HomogenizedSuperposition.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedSuperposition.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), superposition:
adding the homogeneous and forced solutions adds their prepared initial
loads and their L² forcing in the actual weak memory equation. -/
theorem IsHomogenizedSolution.add {T : ℝ} (hT : 0 < T)
    (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d) (hK : Continuous K)
    (g₀ g₁ : SpatialL2 Ω) (f₀ f₁ : Forcing Ω T)
    (u v : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsHomogenizedSolution hT Vhom Ehom K g₀ f₀ u)
    (hv : IsHomogenizedSolution hT Vhom Ehom K g₁ f₁ v) :
    IsHomogenizedSolution hT Vhom Ehom K (g₀ + g₁) (f₀ + f₁) (u + v) := by
  sorry

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel assembly:
the forced equation for a trajectory difference and the homogeneous
equation recover the equation with the original initial load and forcing. -/
theorem IsHomogenizedSolution.of_sub {T : ℝ} (hT : 0 < T)
    (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d) (hK : Continuous K)
    (g : SpatialL2 Ω) (f : Forcing Ω T)
    (u v : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsHomogenizedSolution hT Vhom Ehom K 0 f (u - v))
    (hv : IsHomogenizedSolution hT Vhom Ehom K g 0 v) :
    IsHomogenizedSolution hT Vhom Ehom K g f u := by
  sorry

end KVApproximation.Homogenization
