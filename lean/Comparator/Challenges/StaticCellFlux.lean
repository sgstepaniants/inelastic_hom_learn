module

public import KVApproximation.Homogenization.StaticCellFlux

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Theorem 3.1, static cell corrector: the negative weighted projection
is the symmetric gradient of a unique zero-mean periodic H¹ displacement. -/
theorem exists_unique_static_corrector {d : ℕ} (A : CoerciveField d) (e : Symmetric d) :
    ∃! u : ZeroMeanPeriodicH1 d,
      correctorGradientL d u = -(cellProjection A (constantStrainL d e) : StrainField d) := by
  sorry

/-- Theorem 3.1, static oscillating fluxes: the L² flux is represented
by the pointwise coefficient action on the corrected strain. -/
theorem cellFlux_apply_ae {d : ℕ} (A : CoerciveField d) (e : Symmetric d) :
    cellFlux A e =ᵐ[cellMeasure d] fun y =>
      action (A.field y) (e - (cellProjection A (constantStrainL d e) : StrainField d) y) := by
  sorry

/-- Theorem 3.1, static oscillating fluxes: the cell flux annihilates
every periodic displacement strain. -/
theorem cellFlux_orthogonal_periodic {d : ℕ} (A : CoerciveField d) (e : Symmetric d)
    (w : PeriodicH1 d) :
    ⟪cellFlux A e, PeriodicH1.symmetricGradientL d w⟫_ℝ = 0 := by
  sorry

/-- Theorem 3.1 (`eq:homogenized_tensors`): the mean corrected stress
represents the static effective form. -/
theorem cellFlux_mean_pairing {d : ℕ} (A : CoerciveField d) (e f : Symmetric d) :
    ⟪e, ∫ y, cellFlux A f y ∂cellMeasure d⟫_ℝ = effectiveForm A e f := by
  sorry

end KVApproximation.Homogenization
