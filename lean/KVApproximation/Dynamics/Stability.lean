module

public import KVApproximation.Dynamics.DissipativeStability
public import KVApproximation.Dynamics.PronyDissipation
public import KVApproximation.Dynamics.PronyTrajectory

/-!
# Existence and stability of the learned kinetic equation
-/

public section

namespace KVApproximation.Dynamics

variable {M E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Proposition B.13 (`prop:ua_step3_stability`), at a fixed material:
global existence, uniqueness on the half-line, and the finite-time state
estimate, including equality in the trapping-margin condition. -/
theorem kinetic_stability {n : ℕ} (P : PronyModel M E n) (a : M)
    (e : BoundedTrajectory E) {βE βV δ rateLower δIV η εG : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hRateLower : 0 < rateLower) (hRate : ∀ k, rateLower ≤ P.rate k)
    (hδIV : 0 < δIV) (hIV : ∀ t : ℝ, 0 ≤ t → ‖P.state a e t‖ ≤ δIV)
    (hη : 0 < η) (hεG : 0 < εG) (hmargin : εG ≤ rateLower * η)
    (G : E × BlockState n E → BlockState n E) (hG : LocallyLipschitz G)
    (happrox : ∀ (v : E) (q : BlockState n E),
      βV * ‖v‖ ≤ δ → ‖q‖ ≤ δIV + η →
        ‖G (v, q) - P.kineticResponse a v q‖ ≤ εG) :
    ∃ q : BoundedTrajectory (BlockState n E),
      IsKineticSolution e G q ∧
      (∀ q' : BoundedTrajectory (BlockState n E),
        IsKineticSolution e G q' → q.Agree q') ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖q.value t - P.state a e t‖ ≤ εG / rateLower *
          (1 - Real.exp (-rateLower * t))) := by
  obtain ⟨r, hrValue, hr⟩ := pronyState_isKineticSolution P
    (fun k => hRateLower.trans_le (hRate k)) a e
  have hv : βV * e.velocityBound ≤ δ := by
    have hnonneg : 0 ≤ βE * e.valueBound := mul_nonneg hβE.le ENNReal.toReal_nonneg
    change βE * e.valueBound + βV * e.velocityBound ≤ δ at he
    linarith
  obtain ⟨q, hq, hUnique, hError⟩ := dissipative_driven_stability e r
    (fun vq => P.kineticResponse a vq.1 vq.2) G hr hRateLower hδIV
    (fun t ht => by rw [hrValue t ht]; exact hIV t ht) hη hεG hmargin
    (fun v q q' => prony_kinetic_dissipative P a hRate v q q') hG
    (fun v q hv' hq' => happrox v q
      ((mul_le_mul_of_nonneg_left hv' hβV.le).trans hv) hq')
  refine ⟨q, hq, hUnique, ?_⟩
  intro t ht
  simpa only [hrValue t ht] using hError t ht

end KVApproximation.Dynamics
