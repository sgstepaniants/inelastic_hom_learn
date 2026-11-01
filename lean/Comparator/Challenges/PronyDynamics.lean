module

public import KVApproximation.Dynamics.PronyModel
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Internal-variable existence and stability
-/

public section

namespace KVApproximation.Dynamics

variable {M E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Proposition B.10 (`eq:q_i_ode`, `eq:q_i_duhamel`): the convolution
state has bounded value and velocity and solves the Prony initial-value problem. -/
theorem pronyState_isKineticSolution {n : ℕ} (P : PronyModel M E n)
    (hRate : ∀ k, 0 < P.rate k) (a : M) (e : BoundedTrajectory E) :
    ∃ q : BoundedTrajectory (BlockState n E),
      (∀ t : ℝ, 0 ≤ t → q.value t = P.state a e t) ∧
      IsKineticSolution e (fun vq => P.kineticResponse a vq.1 vq.2) q := by
  sorry

/-- Proposition B.10 (`eq:q_i_duhamel`, `eq:Kn_def`): summing the
internal-state convolutions is exactly convolution with the finite Prony kernel. -/
theorem pronyStress_eq_kernel_convolution {n : ℕ} (P : PronyModel M E n)
    (a : M) (e : BoundedTrajectory E) {t : ℝ} (ht : 0 ≤ t) :
    P.stress a e t = P.viscosity a (e.velocity t) + P.elasticity a (e.value t) +
      ∫ s in (0 : ℝ)..t, P.kernel a (t - s) (e.velocity s) := by
  sorry

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
  sorry

/-- Proposition B.13 (`eq:ua_err`), stress estimate: summing `n` tensor
blocks introduces precisely the factor `√n`. -/
theorem stress_error_le {n : ℕ} (P : PronyModel M E n) (a : M)
    {e v : E} {q qIV : BlockState n E} {σ : E} {εF εG rateLower : ℝ}
    (hF : ‖σ - P.stressResponse a e v q‖ ≤ εF)
    (hState : ‖q - qIV‖ ≤ εG / rateLower) :
    ‖σ - P.stressResponse a e v qIV‖ ≤ εF + Real.sqrt n * εG / rateLower := by
  sorry

end KVApproximation.Dynamics
