module

public import KVApproximation.NeuralOperators.PronyResponses
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Uniform state bounds and approximation of Prony responses
-/

public section

open KVApproximation.Dynamics KVApproximation.NeuralOperators

namespace KVApproximation.Dynamics

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma B.11 (`lem:ua_step3_targets`), quantitative estimate in its proof:
coefficient bounds and a positive common rate control the Euclidean block norm. -/
theorem prony_state_bound {n : ℕ} (P : PronyModel M E n) (a : M)
    {βE βV δ rateLower : ℝ} (hβE : 0 < βE) (hβV : 0 < βV)
    (hδ : 0 ≤ δ) (hRateLower : 0 < rateLower) (hRate : ∀ k, rateLower ≤ P.rate k)
    (C : Fin n → ℝ) (hC : ∀ k, 0 ≤ C k) (hcoef : ∀ k, ‖P.coefficient k a‖ ≤ C k)
    (e : BoundedTrajectory E) (he : e.Admissible βE βV δ) {t : ℝ} (ht : 0 ≤ t) :
    ‖P.state a e t‖ ≤ δ / (βV * rateLower) * Real.sqrt (∑ k, C k ^ 2) := by
  sorry

/-- Lemma B.11: compactness and coefficient continuity give one positive
state bound for all materials, admissible strains, and nonnegative times. -/
theorem prony_state_uniform_bound {n : ℕ} (P : PronyModel M E n)
    (L : Set M) (hL : IsCompact L) (hcoef : ∀ k, ContinuousOn (P.coefficient k) L)
    {βE βV δ : ℝ} (hβE : 0 < βE) (hβV : 0 < βV) (hδ : 0 < δ)
    (hRate : ∀ k, 0 < P.rate k) :
    ∃ δIV : ℝ, 0 < δIV ∧ ∀ a ∈ L, ∀ e : BoundedTrajectory E,
      e.Admissible βE βV δ → ∀ t : ℝ, 0 ≤ t → ‖P.state a e t‖ ≤ δIV := by
  sorry

end KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lemma B.12 (`lem:ua_step3_no`): simultaneous approximation of both
responses on the prescribed compact domains, with local Lipschitz regularity
for the full kinetic vector input at each material. Mandel transport converts
the block state to the scalar state of dimension `n * dim E`. -/
theorem prony_responses_approximate {n : ℕ} (P : PronyModel M E n)
    (L : Set M) (hL : IsCompact L)
    (hV : ContinuousOn P.viscosity L) (hE : ContinuousOn P.elasticity L)
    (hcoef : ∀ k, ContinuousOn (P.coefficient k) L)
    {βE βV δ radius εF εG : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (hδ : 0 < δ) (hRadius : 0 < radius)
    (hεF : 0 < εF) (hεG : 0 < εG)
    (Fclass : Set C(StressInput E (BlockState n E) × M, E))
    (Gclass : Set C(KineticInput E (BlockState n E) × M, BlockState n E))
    (hF : HasUniversalApproximation Fclass) (hG : HasLocallyLipschitzApproximation Gclass) :
    ∃ F ∈ Fclass, ∃ G ∈ Gclass,
      (∀ a ∈ L, ∀ x ∈ stressInputSet (E := E) (Q := BlockState n E) βE βV δ radius,
        ‖F (x, a) - pronyStressResponse P a x‖ ≤ εF) ∧
      (∀ a ∈ L, ∀ x ∈ kineticInputSet (E := E) (Q := BlockState n E) βV δ radius,
        ‖G (x, a) - pronyKineticResponse P a x‖ ≤ εG) ∧
      ∀ a ∈ L, LocallyLipschitz (fun x => G (x, a)) := by
  sorry

end KVApproximation.NeuralOperators
