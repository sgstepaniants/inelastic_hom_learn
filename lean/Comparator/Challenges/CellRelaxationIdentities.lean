module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Tensor.Isotropic

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Proposition 4.7 (`prop:no_spectral_stability`), limiting operator:
equal viscosity and elasticity fields give the identity relaxation operator,
independently of their stored ellipticity bounds. -/
theorem cellRelaxation_eq_id_of_field_eq {d : ℕ} (V E : CoerciveField d)
    (hfield : V.field = E.field) :
    cellRelaxation V E = ContinuousLinearMap.id ℝ (correctorSubspace d) := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip operator formula:
identity viscosity and an identity coefficient jump add the projection
of the restricted strain. The restriction is represented in actual L². -/
theorem cellRelaxation_eq_add_projection_of_ae_indicator {d : ℕ}
    (V E : CoerciveField d) (S : Set (PeriodicCell d))
    (hV : V.field =ᵐ[cellMeasure d] fun _ => identityElasticity d)
    (hE : E.field =ᵐ[cellMeasure d]
      fun y => identityElasticity d + S.indicator (fun _ => identityElasticity d) y)
    (η : correctorSubspace d) (ξ : StrainField d)
    (hξ : ξ =ᵐ[cellMeasure d] S.indicator (fun y => (η : StrainField d) y)) :
    cellRelaxation V E η = η + cellProjection V ξ := by
  sorry

end KVApproximation.Homogenization
