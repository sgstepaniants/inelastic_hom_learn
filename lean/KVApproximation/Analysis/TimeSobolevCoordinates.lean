module

public import KVApproximation.Analysis.TimeSobolev

/-!
# Value and velocity coordinates of finite-time H¹ trajectories
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, time-space bounds: the L² value coordinate of the actual
finite-time Sobolev space. -/
def TimeH1.valueL2 {T : ℝ} :
    TimeH1 H T →L[ℝ] Lp H 2 (volume.restrict (Set.Ioo 0 T)) :=
  TauCeti.EvolutionSpace.valueL

/-- Theorem 3.1, time-space bounds: the L² velocity coordinate, using
the inverse Riesz isometry on the recorded dual-valued weak derivative. -/
def TimeH1.velocityL2 {T : ℝ} :
    TimeH1 H T →L[ℝ] Lp H 2 (volume.restrict (Set.Ioo 0 T)) :=
  (((InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap).compLpL
    2 (volume.restrict (Set.Ioo 0 T))).comp TauCeti.EvolutionSpace.timeDerivL

end KVApproximation.Analysis
