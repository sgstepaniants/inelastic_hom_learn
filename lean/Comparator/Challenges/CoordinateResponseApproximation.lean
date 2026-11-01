module

public import KVApproximation.NeuralOperators.StateCoordinates

/-!
# Approximation in prescribed state coordinates
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

/-- Lemma B.12: response mappings on the ambient material space approximate
a Prony model defined on its compact material class, in any isometric state
coordinates. A2 retains local Lipschitz regularity in the full kinetic input. -/
theorem prony_responses_approximate_in_coordinates
    {M E Q : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    (L : Set M) (hL : IsCompact L) {n : ℕ} (P : PronyModel L E n)
    (T : BlockState n E ≃ₗᵢ[ℝ] Q)
    (hV : Continuous P.viscosity) (hE : Continuous P.elasticity)
    (hcoef : ∀ k, Continuous (P.coefficient k))
    {βE βV δ radius εF εG : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (hδ : 0 < δ) (hRadius : 0 < radius)
    (hεF : 0 < εF) (hεG : 0 < εG)
    (Fclass : Set C(StressInput E Q × M, E))
    (Gclass : Set C(KineticInput E Q × M, Q))
    (hF : HasUniversalApproximation Fclass) (hG : HasLocallyLipschitzApproximation Gclass) :
    ∃ F ∈ Fclass, ∃ G ∈ Gclass,
      (∀ a : L, ∀ x ∈ stressInputSet (E := E) (Q := Q) βE βV δ radius,
        ‖F (x, a.val) - coordinateStressResponse P T a x‖ ≤ εF) ∧
      (∀ a : L, ∀ x ∈ kineticInputSet (E := E) (Q := Q) βV δ radius,
        ‖G (x, a.val) - coordinateKineticResponse P T a x‖ ≤ εG) ∧
      ∀ a : L, LocallyLipschitz (fun x => G (x, a.val)) := by
  sorry

end KVApproximation.NeuralOperators
