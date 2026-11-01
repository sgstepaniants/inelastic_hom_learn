module

public import KVApproximation.Homogenization.ConstantSpatialForm
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance ConstantSpatialCoercivity.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance ConstantSpatialCoercivity.instNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω) := inferInstance

local instance ConstantSpatialCoercivity.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Theorem 3.1, homogenized spatial coercivity: positive definiteness
of a constant tensor and the Dirichlet Korn estimate give coercivity in the
actual H¹₀ norm on every bounded open domain. -/
theorem constantSpatialFormL_isCoercive (A : Elasticity d) (hA : PositiveDefinite A)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    IsCoercive (constantSpatialFormL (Ω := Ω) A) := by
  sorry

/-- Theorem 3.1, finite-time uniqueness: a positive constant tensor
controls the actual displacement norm by its spatial dual norm. -/
theorem exists_constantSpatialFormL_norm_bound (A : Elasticity d) (hA : PositiveDefinite A)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ZeroBoundaryH1 Ω,
      ‖u‖ ≤ C * ‖constantSpatialFormL (Ω := Ω) A u‖ := by
  sorry

end KVApproximation.Homogenization
