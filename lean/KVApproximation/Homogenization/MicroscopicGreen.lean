module

public import KVApproximation.Homogenization.MicroscopicTrajectory

/-!
# Microscopic Green operators
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicGreen.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) :=
  ZeroBoundaryH1.instNormedAddCommGroup Ω

local instance MicroscopicGreen.instTopologicalRing :
    IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ)
      (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1, Duhamel's formula: evolve the viscous elliptic load map
by the actual microscopic semigroup. The value at zero scale is set to zero. -/
def microscopicGreen (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε t : ℝ) :
    SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω :=
  if hε : ε ≠ 0 then
    (NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)).comp
      (microscopicLoadL V hΩ ε hε)
  else 0

end KVApproximation.Homogenization
