module

public import KVApproximation.Dynamics.PronyModel

/-!
# Dissipation and stress sensitivity of the Prony model
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.Dynamics

variable {M E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proposition B.13 (`eq:G_IV_dissipative`): the common lower rate
controls the exact one-sided state Lipschitz constant. The coefficient
tensors cancel, so no sign assumption on them is needed. -/
theorem prony_kinetic_dissipative {n : ℕ} (P : PronyModel M E n) (a : M)
    {rateLower : ℝ} (hRate : ∀ k, rateLower ≤ P.rate k)
    (v : E) (q q' : BlockState n E) :
    ⟪q - q', P.kineticResponse a v q - P.kineticResponse a v q'⟫_ℝ ≤
      -rateLower * ‖q - q'‖ ^ 2 := by
  sorry

/-- Proposition B.13 (`eq:ua_err`): summing the tensorial state blocks
has Lipschitz constant `sqrt n` in their Euclidean product norm. -/
theorem prony_stress_lipschitz {n : ℕ} (P : PronyModel M E n) (a : M)
    (e v : E) (q q' : BlockState n E) :
    ‖P.stressResponse a e v q - P.stressResponse a e v q'‖ ≤
      Real.sqrt n * ‖q - q'‖ := by
  sorry

end KVApproximation.Dynamics
