module

public import KVApproximation.Approximation.RealResponse
public import KVApproximation.Dynamics.PronyModel
public import KVApproximation.Spectral.TensorActionIntegral

/-!
# Measurability of memory and Prony responses
-/

public section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Proposition B.10: the integrated weighted response is strongly
measurable almost everywhere on the entire nonnegative time axis. -/
theorem aestronglyMeasurable_responseIntegral {d : ℕ} (ν : TensorMeasure d)
    (hνfinite : totalVariation ν Set.univ < ⊤) (c : ℝ)
    (e : Dynamics.BoundedTrajectory (Symmetric d)) :
    AEStronglyMeasurable (fun t => tensorActionIntegral ν (realWeightedResponse c e t))
      Dynamics.timeMeasure := by
  sorry

end KVApproximation.Approximation

namespace KVApproximation.Dynamics

/-- Proposition B.10: the finite Prony stress is measurable even when
the strain velocity is only almost-everywhere measurable. -/
theorem aestronglyMeasurable_pronyStress {M E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (P : PronyModel M E n) (a : M) (e : BoundedTrajectory E) :
    AEStronglyMeasurable (P.stress a e) timeMeasure := by
  sorry

end KVApproximation.Dynamics
