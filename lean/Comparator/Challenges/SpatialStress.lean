module

public import KVApproximation.Homogenization.SpatialOperators

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}
  (A : Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d))))

/-- Theorem 3.1, microscopic stress: the continuous stress map has
the actual coefficient-action representative. -/
theorem spatialStressL_apply_ae (u : ZeroBoundaryH1 Ω) :
    spatialStressL A u =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      action (A x) (VectorH1.symmetricGradientL Ω u.val x) := by
  sorry

/-- Theorem 3.1, microscopic stress bound: Frobenius contraction and
the strain estimate retain constant one on arbitrary open domains. -/
theorem norm_spatialStressL_le (u : ZeroBoundaryH1 Ω) :
    ‖spatialStressL A u‖ ≤ ‖A‖ * ‖u‖ := by
  sorry

/-- Theorem 3.1, weak equilibrium: pairing the actual L² stress with
a Dirichlet strain is the spatial weak form. -/
theorem integral_spatialStressL_strain (u v : ZeroBoundaryH1 Ω) :
    (∫ x in (Ω : Set (PhysicalSpace d)),
      ⟪spatialStressL A u x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) =
        spatialForm A u v := by
  sorry

end KVApproximation.Homogenization
