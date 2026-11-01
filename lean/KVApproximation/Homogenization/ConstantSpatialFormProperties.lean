module

public import KVApproximation.Homogenization.ConstantSpatialForm
public import KVApproximation.Homogenization.SpatialFields
public import KVApproximation.Tensor.LinearActionIdentities
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Constant spatial energy pairings and bounds
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

section TrilinearBound

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

local instance ConstantSpatialFormProperties.instGenericDualNormedGroup :
    NormedAddCommGroup (H →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

local instance ConstantSpatialFormProperties.instGenericDualNormedSpace :
    NormedSpace ℝ (H →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance ConstantSpatialFormProperties.instGenericFormNormedGroup :
    NormedAddCommGroup (H →L[ℝ] H →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

/-- Theorem 3.1, spatial operator bounds: a trilinear bound gives
the nested operator-norm estimate before fixing the Sobolev space. -/
private theorem norm_trilinear_le_one
    (B : F →L[ℝ] H →L[ℝ] H →L[ℝ] ℝ)
    (hB : ∀ A u v, ‖B A u v‖ ≤ ‖A‖ * ‖u‖ * ‖v‖) : ‖B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  exact ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg A) (norm_nonneg u)) (hB A u)

end TrilinearBound

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance ConstantSpatialFormProperties.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance ConstantSpatialFormProperties.instNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω) := inferInstance

local instance ConstantSpatialFormProperties.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

local instance ConstantSpatialFormProperties.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance ConstantSpatialFormProperties.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance ConstantSpatialFormProperties.instFormNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Theorem 3.1, homogenized weak equation: the coefficient-linear
spatial operator has exactly the paper's constant-tensor energy pairing. -/
theorem constantSpatialFormL_apply (A : Elasticity d) (u v : ZeroBoundaryH1 Ω) :
    constantSpatialFormL (Ω := Ω) A u v = spatialForm (fun _ => A) u v := by
  change ⟪(actionL d A).compLp (VectorH1.symmetricGradientL Ω u.val),
    VectorH1.symmetricGradientL Ω v.val⟫_ℝ =
      ∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪symmetricGradient u x, action A (symmetricGradient v x)⟫_ℝ
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(actionL d A).coeFn_compLp (VectorH1.symmetricGradientL Ω u.val),
    symmetricGradientL_apply_ae u, symmetricGradientL_apply_ae v] with x hA hu hv
  rw [hA, actionL_apply, hu, hv, action_symmetric]

/-- Theorem 3.1, memory-operator bound: Frobenius contraction and the
actual H¹ strain map give constant one, on every open spatial domain. -/
theorem norm_constantSpatialFormL_le : ‖constantSpatialFormL (Ω := Ω)‖ ≤ 1 := by
  apply norm_trilinear_le_one
  intro A u v
  change ‖⟪(actionL d A).compLp (VectorH1.symmetricGradientL Ω u.val),
    VectorH1.symmetricGradientL Ω v.val⟫_ℝ‖ ≤ ‖A‖ * ‖u‖ * ‖v‖
  have hM : ‖(actionL d A).compLp (VectorH1.symmetricGradientL Ω u.val)‖ ≤
      ‖A‖ * ‖VectorH1.symmetricGradientL Ω u.val‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(actionL d A).coeFn_compLp (VectorH1.symmetricGradientL Ω u.val)]
      with x hx
    rw [hx, actionL_apply]
    exact norm_action_le A _
  have hu : ‖VectorH1.symmetricGradientL Ω u.val‖ ≤ ‖u‖ :=
    (VectorH1.norm_symmetricGradientL_le u.val).trans (VectorH1.norm_gradientL_le u.val)
  have hv : ‖VectorH1.symmetricGradientL Ω v.val‖ ≤ ‖v‖ :=
    (VectorH1.norm_symmetricGradientL_le v.val).trans (VectorH1.norm_gradientL_le v.val)
  calc
    _ ≤ ‖(actionL d A).compLp (VectorH1.symmetricGradientL Ω u.val)‖ *
        ‖VectorH1.symmetricGradientL Ω v.val‖ :=
      norm_inner_le_norm (𝕜 := ℝ)
        ((actionL d A).compLp (VectorH1.symmetricGradientL Ω u.val))
        (VectorH1.symmetricGradientL Ω v.val)
    _ ≤ ‖A‖ * ‖u‖ * ‖v‖ :=
      mul_le_mul (hM.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg A))) hv
        (norm_nonneg (VectorH1.symmetricGradientL Ω v.val))
        (mul_nonneg (norm_nonneg A) (norm_nonneg u))

end KVApproximation.Homogenization
