module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Homogenization.ConstantSpatialForm
public import KVApproximation.Homogenization.MicroscopicGreen
public import Mathlib.Analysis.Convolution

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

section GreenUniquenessInterface

local instance GreenUniqueness.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance GreenUniqueness.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1, Duhamel's formula: continuous viscously prepared
trajectories satisfying the same cell-memory Green balance agree on the
nonnegative half-line. -/
theorem green_balance_unique
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (g : SpatialL2 Ω) (v w : ℝ → ZeroBoundaryH1 Ω)
    (hv : ContinuousOn v (Set.Ici (0 : ℝ)))
    (hw : ContinuousOn w (Set.Ici (0 : ℝ)))
    (hvb : ∀ t : ℝ, 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (v t) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, v r) +
        posConvolution C.kernel v (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g)
    (hwb : ∀ t : ℝ, 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (w t) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, w r) +
        posConvolution C.kernel w (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g) :
    Set.EqOn v w (Set.Ici (0 : ℝ)) := by
  sorry

end GreenUniquenessInterface

local instance HomogenizedGreen.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedGreen.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), forcing contribution:
the actual microscopic Green operators converge weakly at every nonnegative
time and every spatial L² input to a bounded, time-Lipschitz linear family.
Its constant-load balance uses the actual cell tensors and memory kernel.
The negative-time extension is chosen continuously. -/
theorem exists_homogenizedGreen
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ M : ℝ, 0 < M ∧ ∃ G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω,
      Continuous G ∧
      (∀ t : ℝ, 0 ≤ t → ‖G t‖ ≤ M) ∧
      LipschitzOnWith (Real.toNNReal M) G (Set.Ici (0 : ℝ)) ∧
      (∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
        constantSpatialFormL (Ω := Ω) C.viscosity (G t g) +
          constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, G r g) +
          posConvolution C.kernel (fun r => G r g)
            (constantSpatialFormL (Ω := Ω)) volume t = spatialLoadOperator (Ω := Ω) g) ∧
      ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
        ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
          Tendsto (fun ε => ℓ (microscopicGreen (Ω := Ω) V E hΩ ε t g))
            (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (G t g))) := by
  sorry

end KVApproximation.Homogenization
