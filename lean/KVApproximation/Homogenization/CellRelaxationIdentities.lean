module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.OperatorTheory.FieldFormIdentities
public import KVApproximation.Tensor.IsotropicIdentities

/-!
# Relaxation for equal fields and identity coefficient jumps
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Proposition 4.7, limiting operator: the restricted Riesz map cancels
its inverse when viscosity and elasticity are the same form. -/
private theorem relaxation_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : OperatorTheory.CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    OperatorTheory.relaxation A A X = ContinuousLinearMap.id ℝ X := by
  apply ContinuousLinearMap.ext
  intro u
  exact (A.restrict X).riesz.symm_apply_apply u

/-- Proposition 4.7 (`prop:no_spectral_stability`), limiting operator:
equal viscosity and elasticity fields give the identity relaxation operator,
independently of their stored ellipticity bounds. -/
theorem cellRelaxation_eq_id_of_field_eq {d : ℕ} (V E : CoerciveField d)
    (hfield : V.field = E.field) :
    cellRelaxation V E = ContinuousLinearMap.id ℝ (correctorSubspace d) := by
  change OperatorTheory.relaxation V.toForm E.toForm (correctorSubspace d) = _
  rw [← CoerciveField.toForm_congr hfield]
  exact relaxation_self V.toForm (correctorSubspace d)

/-- Proposition 4.7, identity viscosity: its actual Riesz map acts as
the identity on every periodic strain field. -/
private theorem riesz_apply_of_ae_identity {d : ℕ} (A : CoerciveField d)
    (hA : A.field =ᵐ[cellMeasure d] fun _ => identityElasticity d)
    (w : StrainField d) : A.toForm.riesz w = w := by
  have hmul : A.toForm.riesz w = multiplication A.field w :=
    congrArg (fun L : StrainField d →L[ℝ] StrainField d => L w) A.riesz_eq_multiplication
  rw [hmul]
  apply Lp.ext
  filter_upwards [multiplication_apply_ae A.field w, hA] with y hy hAy
  exact hy.trans (by rw [hAy, action_identityElasticity])

/-- Proposition 4.7, coefficient jump: multiplication by the jump tensor
adds the L² restriction of the strain. -/
private theorem riesz_apply_of_ae_indicator {d : ℕ}
    (E : CoerciveField d) (S : Set (PeriodicCell d))
    (hE : E.field =ᵐ[cellMeasure d]
      fun y => identityElasticity d + S.indicator (fun _ => identityElasticity d) y)
    (w ξ : StrainField d) (hξ : ξ =ᵐ[cellMeasure d] S.indicator w) :
    E.toForm.riesz w = w + ξ := by
  have hmul : E.toForm.riesz w = multiplication E.field w :=
    congrArg (fun L : StrainField d →L[ℝ] StrainField d => L w) E.riesz_eq_multiplication
  rw [hmul]
  apply Lp.ext
  filter_upwards [multiplication_apply_ae E.field w, hE, hξ, Lp.coeFn_add w ξ]
    with y hy hEy hξy hadd
  refine hy.trans (Eq.trans ?_ hadd.symm)
  change action (E.field y) (w y) = w y + ξ y
  rw [hEy, hξy]
  change (actionL d
    (identityElasticity d + S.indicator (fun _ => identityElasticity d) y)) (w y) = _
  rw [map_add, add_apply, actionL_apply, action_identityElasticity]
  by_cases hmem : y ∈ S
  · simp only [Set.indicator_of_mem hmem, actionL_apply, action_identityElasticity]
  · simp only [Set.indicator_of_notMem hmem, map_zero, zero_apply]

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
  have hinv (w : StrainField d) : V.toForm.riesz.symm w = w := by
    have h := V.toForm.riesz.symm_apply_apply w
    rw [riesz_apply_of_ae_identity V hV w] at h
    exact h
  calc
    cellRelaxation V E η =
        cellProjection V (V.toForm.riesz.symm (E.toForm.riesz (η : StrainField d))) :=
      OperatorTheory.relaxation_eq_projection_riesz V.toForm E.toForm (correctorSubspace d) η
    _ = cellProjection V (E.toForm.riesz (η : StrainField d)) :=
      congrArg (cellProjection V) (hinv _)
    _ = cellProjection V ((η : StrainField d) + ξ) :=
      congrArg (cellProjection V) (riesz_apply_of_ae_indicator E S hE _ ξ hξ)
    _ = cellProjection V (η : StrainField d) + cellProjection V ξ :=
      (cellProjection V).map_add _ _
    _ = η + cellProjection V ξ :=
      congrArg (fun u => u + cellProjection V ξ)
        (OperatorTheory.projection_eq_self V.toForm (correctorSubspace d) η)

end KVApproximation.Homogenization
