module

public import KVApproximation.Homogenization.SpatialOperators
public import KVApproximation.Homogenization.SpatialFields
public import KVApproximation.Tensor.LinearActionIdentities

/-!
# Spatial energy identities
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}
  (A : Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d))))

private theorem spatialMultiplication_apply_ae
    (e : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    (actionL d).holderL (volume.restrict (Ω : Set (PhysicalSpace d))) ⊤ 2 2 A e
      =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x => action (A x) (e x) := by
  exact (actionL d).coeFn_holder (r := 2) A e

/-- Theorem 3.1, weak elliptic formulation: bounded coefficients and
L² strains give an integrable energy pairing on any open domain. -/
theorem integrable_spatialForm (u v : ZeroBoundaryH1 Ω) :
    Integrable (fun x => ⟪symmetricGradient u x,
      action (A x) (symmetricGradient v x)⟫_ℝ)
        (volume.restrict (Ω : Set (PhysicalSpace d))) := by
  let z := (actionL d).holderL (volume.restrict (Ω : Set (PhysicalSpace d))) ⊤ 2 2 A
    (VectorH1.symmetricGradientL Ω v.val)
  apply (L2.integrable_inner (𝕜 := ℝ) (VectorH1.symmetricGradientL Ω u.val) z).congr
  filter_upwards [spatialMultiplication_apply_ae A (VectorH1.symmetricGradientL Ω v.val),
    symmetricGradientL_apply_ae u, symmetricGradientL_apply_ae v] with x hz hu hv
  change ⟪VectorH1.symmetricGradientL Ω u.val x, z x⟫_ℝ = _
  rw [hu, hz, hv]

/-- Theorem 3.1, static elliptic problems: the constructed continuous
form equals the spatial weak form in the paper. -/
theorem boundedSpatialForm_apply (u v : ZeroBoundaryH1 Ω) :
    boundedSpatialForm A u v = spatialForm A u v := by
  change ⟪(actionL d).holderL (volume.restrict (Ω : Set (PhysicalSpace d))) ⊤ 2 2 A
    (VectorH1.symmetricGradientL Ω u.val), VectorH1.symmetricGradientL Ω v.val⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spatialMultiplication_apply_ae A (VectorH1.symmetricGradientL Ω u.val),
    symmetricGradientL_apply_ae u, symmetricGradientL_apply_ae v] with x hz hu hv
  rw [hz, hu, hv, action_symmetric]

/-- Theorem 3.1, static elliptic problems: major coefficient symmetry
gives symmetry of the spatial form. -/
theorem boundedSpatialForm_symmetric (u v : ZeroBoundaryH1 Ω) :
    boundedSpatialForm A u v = boundedSpatialForm A v u := by
  rw [boundedSpatialForm_apply, boundedSpatialForm_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    (action_symmetric (A x) (symmetricGradient u x) (symmetricGradient v x)).symm.trans
      (real_inner_comm _ _)

noncomputable section SpatialLoad

local instance SpatialFormIdentities.instLoadNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance SpatialFormIdentities.instLoadNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω) := inferInstance

local instance SpatialFormIdentities.instLoadDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Theorem 3.1, microscopic forcing: the continuous dual load map
equals the actual spatial L² pairing. -/
theorem spatialLoadOperator_apply (f : SpatialL2 Ω) (v : ZeroBoundaryH1 Ω) :
    spatialLoadOperator (Ω := Ω) f v = loadPairing f v := by
  rw [loadPairing_eq_inner]
  rfl

/-- Theorem 3.1, uniform forcing bound: the spatial load map retains
constant one in the full H¹ dual norm. -/
theorem norm_spatialLoadOperator_apply_le (f : SpatialL2 Ω) :
    ‖spatialLoadOperator (Ω := Ω) f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro v
  rw [Real.norm_eq_abs, spatialLoadOperator_apply]
  exact abs_loadPairing_le f v

end SpatialLoad

end KVApproximation.Homogenization
