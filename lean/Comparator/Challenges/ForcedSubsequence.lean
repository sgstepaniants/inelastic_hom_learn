module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Homogenization.ConstantSpatialForm
public import KVApproximation.Homogenization.SpatialOperators
public import KVApproximation.Homogenization.WeakProblem
public import Mathlib.Analysis.Convolution

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance ForcedSubsequence.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance ForcedSubsequence.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1, forced compactness: the prescribed Duhamel trace of an
actual weak H¹ limit identifies its full homogenized memory equation. -/
theorem forced_subsequence_of_trace
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω) (f : Forcing Ω T)
    (uHom : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hHom : IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ 0 uHom)
    (G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω) (hG : Continuous G)
    (hbalance : ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (G t g) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, G r g) +
        posConvolution C.kernel (fun r => G r g)
          (constantSpatialFormL (Ω := Ω)) volume t = spatialLoadOperator (Ω := Ω) g)
    (u : ℕ → TimeH1 (ZeroBoundaryH1 Ω) T) {B : ℝ} (hbound : ∀ n, ‖u n‖ ≤ B)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T, ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (TimeH1.trace hT (u n) t)) atTop
        (𝓝 (ℓ ((∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) +
          TimeH1.trace hT uHom t)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f uLim ∧
      ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  sorry

end KVApproximation.Homogenization
