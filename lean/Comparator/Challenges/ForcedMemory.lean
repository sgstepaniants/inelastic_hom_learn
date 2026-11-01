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

local instance ForcedMemory.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance ForcedMemory.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel forcing:
an actual H¹ realization of the spatial Green convolution satisfies the
homogenized weak equation with L² forcing and zero initial displacement. -/
theorem green_trace_isHomogenizedSolution {T : ℝ} (hT : 0 < T)
    (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d) (hK : Continuous K)
    (G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω) (hG : Continuous G)
    (hbalance : ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
      constantSpatialFormL (Ω := Ω) Vhom (G t g) +
        constantSpatialFormL (Ω := Ω) Ehom (∫ r in (0 : ℝ)..t, G r g) +
        posConvolution K (fun r => G r g) (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g)
    (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T,
      TimeH1.trace hT u t = ∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) :
    TimeH1.initial hT u = 0 ∧ IsHomogenizedSolution hT Vhom Ehom K 0 f u := by
  sorry

end KVApproximation.Homogenization
