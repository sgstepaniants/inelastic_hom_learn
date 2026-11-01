module

public import KVApproximation.Homogenization.ConstantSpatialForm
public import KVApproximation.Homogenization.SpatialOperators
public import KVApproximation.Homogenization.WeakProblem
public import Mathlib.Analysis.Convolution

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogenizedMemory.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedMemory.instNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedMemory.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedMemory.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`eq:homogenized_model_identified`): the actual spatial
weak formulation is the dual-valued memory equation, with its prepared
initial condition and one common exceptional time-null set. -/
theorem isHomogenizedSolution_iff_memory_equation {T : ℝ} (hT : 0 < T)
    (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d) (hK : Continuous K)
    (g₀ : SpatialL2 Ω) (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T) :
    IsHomogenizedSolution hT Vhom Ehom K g₀ f u ↔
      constantSpatialFormL (Ω := Ω) Ehom (TimeH1.initial hT u) =
          spatialLoadOperator (Ω := Ω) g₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          constantSpatialFormL (Ω := Ω) Vhom (TimeH1.velocity u t) +
            constantSpatialFormL (Ω := Ω) Ehom (TimeH1.value u t) +
            posConvolution K (TimeH1.velocity u) (constantSpatialFormL (Ω := Ω)) volume t =
              spatialLoadOperator (Ω := Ω) (f t) := by
  sorry

end KVApproximation.Homogenization
