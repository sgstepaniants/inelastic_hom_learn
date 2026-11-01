module

public import KVApproximation.Homogenization.SpatialEvolutionOperators
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Homogeneous microscopic trajectories
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicTrajectory.instNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) :=
  inferInstance

local instance MicroscopicTrajectory.instTopologicalRing :
    IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ)
      (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1, homogeneous evolution: the actual spatial semigroup
trajectory, defined on the real axis and used on nonnegative times. -/
def microscopicTrajectory (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0)
    (q : ZeroBoundaryH1 Ω) (t : ℝ) : ZeroBoundaryH1 Ω :=
  (NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q

end KVApproximation.Homogenization
