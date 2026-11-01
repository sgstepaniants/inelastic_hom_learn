module

public import KVApproximation.Homogenization.StaticWeakProblem
public import KVApproximation.Analysis.VectorSobolevFields
public import KVApproximation.Tensor.LinearAction
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Constant tensors as spatial energy operators
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance ConstantSpatialForm.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance ConstantSpatialForm.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

/-- Theorem 3.1, homogenized weak equation: a constant elasticity tensor
acts on Dirichlet displacements through their actual L² symmetric gradients.
The coefficient dependence is a continuous linear map into spatial forms. -/
def constantSpatialFormL :
    Elasticity d →L[ℝ] ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω →L[ℝ] ℝ :=
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  let F := Lp (Symmetric d) 2 μ
  letI : IsNormableSpace ℝ F :=
    ⟨⟨normSeminorm ℝ F, norm_withSeminorms ℝ F⟩⟩
  let S : ZeroBoundaryH1 Ω →L[ℝ] F :=
    (VectorH1.symmetricGradientL Ω).comp (zeroBoundarySubmodule Ω).toSubmodule.subtypeL
  let M : Elasticity d →L[ℝ] F →L[ℝ] F := (actionL d).compLpL₂ 2 μ
  let J : F →L[ℝ] ZeroBoundaryH1 Ω →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ (ZeroBoundaryH1 Ω) F ℝ).flip S).comp
      (innerSL ℝ (E := F))
  ((ContinuousLinearMap.compL ℝ (ZeroBoundaryH1 Ω) F
      (ZeroBoundaryH1 Ω →L[ℝ] ℝ)) J).comp
    (((ContinuousLinearMap.compL ℝ (ZeroBoundaryH1 Ω) F F).flip S).comp M)

end KVApproximation.Homogenization
