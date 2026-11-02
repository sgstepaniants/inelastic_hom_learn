module

public import KVApproximation.Analysis.DirichletFields

/-!
# Dual-space structures for Green balances

The independent Green challenge and its proofs share these supporting
structures, so their statement dependencies use identical definitions.
-/

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

section

local instance GreenUniqueness.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance GreenUniqueness.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end

section

local instance HomogenizedGreen.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedGreen.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end

end KVApproximation.Homogenization
