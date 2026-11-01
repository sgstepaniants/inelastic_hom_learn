module

public import KVApproximation.Approximation.RealResponseIdentities
public import KVApproximation.Dynamics.DampedResponseProperties
public import KVApproximation.Spectral.TensorActionFubini

/-!
# Measurability of the integrated weighted response
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Proposition B.10: the integrated weighted response is strongly
measurable almost everywhere on the entire nonnegative time axis. -/
theorem aestronglyMeasurable_responseIntegral {d : ℕ} (ν : TensorMeasure d)
    (hνfinite : totalVariation ν Set.univ < ⊤) (c : ℝ)
    (e : BoundedTrajectory (Symmetric d)) :
    AEStronglyMeasurable (fun t => tensorActionIntegral ν (realWeightedResponse c e t))
      timeMeasure := by
  let : NormedAddCommGroup (Symmetric d) := (symmetricSubmodule d).normedAddCommGroup
  let : NormedSpace ℝ (Symmetric d) := (symmetricSubmodule d).normedSpace
  let : NormedAddCommGroup (Elasticity d) := (elasticitySubmodule d).normedAddCommGroup
  let : NormedSpace ℝ (Elasticity d) := (elasticitySubmodule d).normedSpace
  let : IsFiniteMeasure ν.variation := ⟨hνfinite⟩
  let f (t r : ℝ) := realWeightedResponse c e (max t 0) r
  have htime (r : ℝ) : Continuous (fun t => f t r) := by
    change Continuous (fun t : ℝ => (c + r) • dampedResponse r e.velocity (max t 0))
    have hd := continuousOn_dampedResponse r e.velocity
      (fun T hT => e.velocity_intervalIntegrable le_rfl hT)
    exact (continuous_const : Continuous (fun _ : ℝ => c + r)).smul
      (hd.comp_continuous (continuous_id.max continuous_const)
      (fun t => le_max_right t 0))
  have hjoint : StronglyMeasurable (Function.uncurry f) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable htime
      (fun t => (continuous_realWeightedResponse c e (le_max_right t 0)).stronglyMeasurable)
  have hi : StronglyMeasurable (fun t => tensorActionIntegral ν (f t)) :=
    hjoint.integral_vectorMeasure_prod_right
  apply hi.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  simp only [f, max_eq_left ht]

end KVApproximation.Approximation
