module

public import KVApproximation.Approximation.RealResponse
public import KVApproximation.Approximation.WeightedResponseAnalytic
public import TauCeti.Analysis.Normed.Module.Complexification

/-!
# Real restrictions of the analytic weighted response
-/

public section

open MeasureTheory
open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Lemma B.7 and Proposition B.10: real-linear embedding of the real
weighted response agrees with the analytic response at real rates. -/
theorem map_realWeightedResponse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →L[ℝ] F) (c : ℝ) (e : BoundedTrajectory E)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    J (realWeightedResponse c e t r) = weightedResponse J c e t r := by
  have hi : IntervalIntegrable (fun s => Real.exp (-r * (t - s)) • e.velocity s)
      volume 0 t :=
    (e.velocity_intervalIntegrable le_rfl ht).continuousOn_smul (by fun_prop)
  have hexp (s : ℝ) : Complex.exp (-(r : ℂ) * ((t - s : ℝ) : ℂ)) =
      (Real.exp (-r * (t - s)) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]
  unfold realWeightedResponse dampedResponse weightedResponse
  rw [J.map_smul, ← J.intervalIntegral_comp_comm hi]
  simp only [J.map_smul, hexp]
  simp only [← Complex.ofReal_add, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- Proposition B.10: the real weighted response is continuous in the
spectral rate for every finite nonnegative time. -/
theorem continuous_realWeightedResponse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ) (e : BoundedTrajectory E) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (realWeightedResponse c e t) := by
  let J := (TauCeti.Complexification.ofRealLI E).toContinuousLinearMap
  have ha := (weightedResponse_entire J c e ht).continuousOn
  have hc : Continuous (fun r : ℝ => weightedResponse J c e t (r : ℂ)) :=
    continuousOn_univ.mp ha |>.comp Complex.continuous_ofReal
  have hr := (TauCeti.Complexification.reCLM E).continuous.comp hc
  convert hr using 1
  funext r
  dsimp only [Function.comp_apply]
  rw [← map_realWeightedResponse J c e ht r]
  simp [J]

end KVApproximation.Approximation
