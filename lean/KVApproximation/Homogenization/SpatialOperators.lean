module

public import KVApproximation.Homogenization.StaticWeakProblem
public import KVApproximation.Analysis.VectorSobolevFields
public import KVApproximation.Tensor.LinearAction
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Bounded spatial elasticity and load forms
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, microscopic stress: coefficient multiplication maps
the actual Dirichlet strain continuously into L² symmetric stresses. -/
def spatialStressL
    (A : Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    ZeroBoundaryH1 Ω →L[ℝ] Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
  ((actionL d).holderL (volume.restrict (Ω : Set (PhysicalSpace d))) ⊤ 2 2 A).comp
    ((VectorH1.symmetricGradientL Ω).comp (zeroBoundarySubmodule Ω).toSubmodule.subtypeL)

/-- Theorem 3.1, static elliptic problems: the actual coefficient
multiplies the L² strain, producing a continuous bilinear form on H¹₀. -/
def boundedSpatialForm
    (A : Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω →L[ℝ] ℝ :=
  letI : IsNormableSpace ℝ (Lp (Symmetric d) 2
      (volume.restrict (Ω : Set (PhysicalSpace d)))) :=
    ⟨⟨normSeminorm ℝ (Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d)))),
      norm_withSeminorms ℝ (Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))⟩⟩
  let S : ZeroBoundaryH1 Ω →L[ℝ]
      Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
    (VectorH1.symmetricGradientL Ω).comp
    (zeroBoundarySubmodule Ω).toSubmodule.subtypeL
  let M : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) →L[ℝ]
      Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
    (actionL d).holderL (volume.restrict (Ω : Set (PhysicalSpace d))) ⊤ 2 2 A
  ((innerSL ℝ (E := Lp (Symmetric d) 2
    (volume.restrict (Ω : Set (PhysicalSpace d))))).comp M).bilinearComp S S

/-- Theorem 3.1, static elliptic problems: the L² load acts on the
actual displacement values as a continuous linear functional. -/
def spatialLoadL (f : SpatialL2 Ω) : ZeroBoundaryH1 Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp ((VectorH1.valueL Ω).comp
    (zeroBoundarySubmodule Ω).toSubmodule.subtypeL)

/-- Theorem 3.1, spatial forcing: L² loads act continuously on
Dirichlet displacements through their actual L² values. -/
def spatialLoadOperator : SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω →L[ℝ] ℝ :=
  letI : IsNormableSpace ℝ (SpatialL2 Ω) :=
    ⟨⟨normSeminorm ℝ (SpatialL2 Ω), norm_withSeminorms ℝ (SpatialL2 Ω)⟩⟩
  (innerSL ℝ (E := SpatialL2 Ω)).bilinearComp (ContinuousLinearMap.id ℝ (SpatialL2 Ω))
    ((VectorH1.valueL Ω).comp (zeroBoundarySubmodule Ω).toSubmodule.subtypeL)

end KVApproximation.Homogenization
