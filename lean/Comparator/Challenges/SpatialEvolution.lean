module

public import KVApproximation.Homogenization.SpatialEvolutionOperators

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance spatialEvolutionNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) :=
  { (inferInstance : SeminormedAddCommGroup (ZeroBoundaryH1 Ω)) with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Theorem 3.1, microscopic forms: the coercive spatial form equals
the actual periodically rescaled weak form. -/
theorem periodicSpatialForm_apply (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0)
    (u v : ZeroBoundaryH1 Ω) :
    (periodicSpatialForm A hΩ ε hε).form u v =
      spatialForm (rescalePeriodic A.field ε) u v := by
  sorry

/-- Theorem 3.1, uniform microscopic energy bounds: positive lower and
upper constants can be chosen before every nonzero rescaling. -/
theorem exists_uniform_periodicSpatialForm_bounds (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ (ε : ℝ) (hε : ε ≠ 0),
      (periodicSpatialForm A hΩ ε hε).HasBounds α β := by
  sorry

/-- Theorem 3.1, homogeneous microscopic evolution: the generator
represents the actual elastic form in the actual viscous pairing. -/
theorem microscopicRelaxation_spec (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0)
    (u v : ZeroBoundaryH1 Ω) :
    spatialForm (rescalePeriodic V.field ε) (microscopicRelaxation V E hΩ ε hε u) v =
      spatialForm (rescalePeriodic E.field ε) u v := by
  sorry

/-- Theorem 3.1, viscous preparation for Duhamel's formula: the
continuous load map solves the actual viscous elliptic equation. -/
theorem microscopicLoadL_spec (V : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0)
    (f : SpatialL2 Ω) (v : ZeroBoundaryH1 Ω) :
    spatialForm (rescalePeriodic V.field ε) (microscopicLoadL V hΩ ε hε f) v =
      loadPairing f v := by
  sorry

/-- Theorem 3.1, uniform evolution operators: one constant bounds
the microscopic generator and viscous load map before choosing the scale. -/
theorem exists_uniform_microscopic_operator_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0),
      (∀ u : ZeroBoundaryH1 Ω, ‖microscopicRelaxation V E hΩ ε hε u‖ ≤ C * ‖u‖) ∧
      (∀ f : SpatialL2 Ω, ‖microscopicLoadL V hΩ ε hε f‖ ≤ C * ‖f‖) := by
  sorry

end KVApproximation.Homogenization
