module

public import KVApproximation.NeuralOperators.PronyResponseStability

/-!
# Material-uniform stability of Prony response approximations
-/

public section

open MeasureTheory KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

/-- Proposition B.13 (`eq:ua_err`): one pair of material-dependent
responses gives unique bounded trajectories and the exact state and stress
error supremums over every material and admissible strain. -/
theorem uniform_prony_response_stability
    {A M E Q : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [FiniteDimensional ℝ Q]
    {n : ℕ} (P : PronyModel A E n) (ι : A → M) (T : BlockState n E ≃ₗᵢ[ℝ] Q)
    {βE βV δ rateLower δIV η εF εG : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV)
    (hRateLower : 0 < rateLower) (hRate : ∀ k, rateLower ≤ P.rate k)
    (hδIV : 0 < δIV)
    (hIV : ∀ (a : A) (e : BoundedTrajectory E), e.Admissible βE βV δ →
      ∀ t : ℝ, 0 ≤ t → ‖P.state a e t‖ ≤ δIV)
    (hη : 0 < η) (hεF : 0 < εF) (hεG : 0 < εG) (hmargin : εG ≤ rateLower * η)
    (F : C(StressInput E Q × M, E)) (G : C(KineticInput E Q × M, Q))
    (hG : ∀ a : A, LocallyLipschitz (fun x => G (x, ι a)))
    (hFapprox : ∀ (a : A) (x) (_ : x ∈ stressInputSet βE βV δ (δIV + η)),
      ‖F (x, ι a) - coordinateStressResponse P T a x‖ ≤ εF)
    (hGapprox : ∀ (a : A) (x) (_ : x ∈ kineticInputSet βV δ (δIV + η)),
      ‖G (x, ι a) - coordinateKineticResponse P T a x‖ ≤ εG) :
    ∃ q : A → {e : BoundedTrajectory E // e.Admissible βE βV δ} → BoundedTrajectory Q,
      (∀ a e, IsResponseSolution G (ι a) e.val (q a e) ∧
        ∀ q' : BoundedTrajectory Q, IsResponseSolution G (ι a) e.val q' → (q a e).Agree q') ∧
      (⨆ a, ⨆ e, eLpNorm (fun t => (q a e).value t - T (P.state a e.val t))
        ⊤ timeMeasure) ≤ ENNReal.ofReal (εG / rateLower) ∧
      (⨆ a, ⨆ e, eLpNorm (fun t => stressAlong F (ι a) e.val (q a e) t - P.stress a e.val t)
        ⊤ timeMeasure) ≤ ENNReal.ofReal (εF + Real.sqrt n * εG / rateLower) := by
  classical
  let Fa (a : A) : C(StressInput E Q, E) :=
    ⟨fun x => F (x, ι a), F.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let Ga (a : A) : C(KineticInput E Q, Q) :=
    ⟨fun x => G (x, ι a), G.continuous.comp (continuous_id.prodMk continuous_const)⟩
  choose q hsol huniq hfinite hstate hstress using
    fun (a : A) (e : {e : BoundedTrajectory E // e.Admissible βE βV δ}) =>
      prony_response_stability P a T e.val hβE hβV e.prop hRateLower hRate hδIV
        (hIV a e.val e.prop) hη hεF hεG hmargin (Fa a) (Ga a) (hG a)
        (hFapprox a) (hGapprox a)
  refine ⟨q, fun a e => ⟨hsol a e, huniq a e⟩, ?_, ?_⟩
  · exact iSup_le fun a => iSup_le fun e => hstate a e
  · exact iSup_le fun a => iSup_le fun e => hstress a e

end KVApproximation.NeuralOperators
