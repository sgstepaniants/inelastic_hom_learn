module

public import KVApproximation.Homogenization.MicroscopicGreen

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, viscous preparation in Duhamel's formula: applying the
Green operator is the homogeneous trajectory of the viscous elliptic load. -/
theorem microscopicGreen_apply (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (t : ℝ) (g : SpatialL2 Ω) :
    microscopicGreen (Ω := Ω) V E hΩ ε t g =
      microscopicTrajectory (Ω := Ω) V E hΩ ε hε
        (microscopicLoadL (Ω := Ω) V hΩ ε hε g) t := by
  sorry

/-- Theorem 3.1, domination of the forcing contribution: one positive
constant bounds every Green operator on the nonnegative half-line and
their time Lipschitz constants in operator norm, before the scale is chosen. -/
theorem exists_uniform_microscopicGreen_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ,
      (∀ t : ℝ, 0 ≤ t → ‖microscopicGreen (Ω := Ω) V E hΩ ε t‖ ≤ C) ∧
      LipschitzOnWith (Real.toNNReal C)
        (microscopicGreen (Ω := Ω) V E hΩ ε) (Set.Ici (0 : ℝ)) := by
  sorry

end KVApproximation.Homogenization
