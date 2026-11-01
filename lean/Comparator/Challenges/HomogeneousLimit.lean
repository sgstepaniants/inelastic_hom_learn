module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Homogenization.WeakProblem
public import KVApproximation.Homogenization.MicroscopicTrajectory
public import KVApproximation.Homogenization.ConstantSpatialForm
public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.Analysis.Convolution

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

-- Use the same named norm structures in the independent interface.
local instance HomogeneousLimit.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogeneousLimit.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), identification
of a homogeneous subsequential limit: weak convergence of prepared initial
states and their microscopic Laplace transforms gives the actual homogenized
weak equation with the cell tensors and memory kernel. -/
theorem homogeneous_limit_isHomogenizedSolution
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) (hpos : ∀ n, 0 < ε n)
    (q : ℕ → ZeroBoundaryH1 Ω) (g₀ : SpatialL2 Ω)
    (hq : ∀ n, ∀ w : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic E.field (ε n)) (q n) w = loadPairing g₀ w)
    (u : TimeH1 (ZeroBoundaryH1 Ω) T) (v : ℝ → ZeroBoundaryH1 Ω)
    (hv : ContinuousOn v (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace hT u t = v t)
    (hqWeak : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (q n)) atTop (𝓝 (ℓ (TimeH1.initial hT u))))
    (hLapWeak : ∀ s : ℝ, 0 < s → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (halfLineLaplace
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s))
          atTop (𝓝 (ℓ (halfLineLaplace v s)))) :
    IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ 0 u := by
  sorry

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel's
homogeneous evolutions: a viscously prepared Laplace limit satisfies the
constant-load Green balance with the actual cell tensors and kernel. -/
theorem viscous_limit_green_balance
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) (hpos : ∀ n, 0 < ε n)
    (q : ℕ → ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ n, ∀ w : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic V.field (ε n)) (q n) w = loadPairing g w)
    (v : ℝ → ZeroBoundaryH1 Ω) (hv : ContinuousOn v (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M)
    (hLapWeak : ∀ s : ℝ, 0 < s → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (halfLineLaplace
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s))
          atTop (𝓝 (ℓ (halfLineLaplace v s)))) :
    ∀ t : ℝ, 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (v t) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, v r) +
        posConvolution C.kernel v (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g := by
  sorry

end KVApproximation.Homogenization
