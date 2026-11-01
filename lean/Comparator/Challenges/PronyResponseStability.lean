module

public import KVApproximation.NeuralOperators.StateCoordinates
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform Prony response bounds in isometric state coordinates
-/

public section

open MeasureTheory KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

/-- Proposition B.13 (`eq:ua_err`): at every material and admissible
strain, the same response tolerances give the unique scalar-coordinate
trajectory and the two full-half-line essential-supremum error bounds. -/
theorem prony_response_stability
    {M E Q : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    [CompleteSpace Q] [FiniteDimensional ℝ Q]
    {n : ℕ} (P : PronyModel M E n) (a : M) (T : BlockState n E ≃ₗᵢ[ℝ] Q)
    (e : BoundedTrajectory E) {βE βV δ rateLower δIV η εF εG : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hRateLower : 0 < rateLower) (hRate : ∀ k, rateLower ≤ P.rate k)
    (hδIV : 0 < δIV) (hIV : ∀ t : ℝ, 0 ≤ t → ‖P.state a e t‖ ≤ δIV)
    (hη : 0 < η) (_hεF : 0 < εF) (hεG : 0 < εG) (hmargin : εG ≤ rateLower * η)
    (F : C(StressInput E Q, E)) (G : C(KineticInput E Q, Q)) (hG : LocallyLipschitz G)
    (hFapprox : ∀ x ∈ stressInputSet βE βV δ (δIV + η),
      ‖F x - coordinateStressResponse P T a x‖ ≤ εF)
    (hGapprox : ∀ x ∈ kineticInputSet βV δ (δIV + η),
      ‖G x - coordinateKineticResponse P T a x‖ ≤ εG) :
    ∃ q : BoundedTrajectory Q,
      IsKineticSolution e (fun vq => G (WithLp.toLp 2 vq)) q ∧
      (∀ q' : BoundedTrajectory Q,
        IsKineticSolution e (fun vq => G (WithLp.toLp 2 vq)) q' → q.Agree q') ∧
      (∀ t : ℝ, 0 ≤ t → ‖q.value t - T (P.state a e t)‖ ≤
        εG / rateLower * (1 - Real.exp (-rateLower * t))) ∧
      eLpNorm (fun t => q.value t - T (P.state a e t)) ⊤ timeMeasure ≤
        ENNReal.ofReal (εG / rateLower) ∧
      eLpNorm (fun t => F (WithLp.toLp 2
        (e.value t, WithLp.toLp 2 (e.velocity t, q.value t))) - P.stress a e t)
        ⊤ timeMeasure ≤ ENNReal.ofReal (εF + Real.sqrt n * εG / rateLower) := by
  sorry

end KVApproximation.NeuralOperators
