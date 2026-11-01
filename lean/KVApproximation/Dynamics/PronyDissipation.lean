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
  rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hd : (P.kineticResponse a v q - P.kineticResponse a v q') k =
      -P.rate k • (q - q') k := by
    simp only [PronyModel.kineticResponse, PiLp.sub_apply]
    module
  rw [hd, real_inner_smul_right, real_inner_self_eq_norm_sq]
  exact mul_le_mul_of_nonneg_right (neg_le_neg (hRate k)) (sq_nonneg _)

/-- Proposition B.13 (`eq:ua_err`): summing the tensorial state blocks
has Lipschitz constant `sqrt n` in their Euclidean product norm. -/
theorem prony_stress_lipschitz {n : ℕ} (P : PronyModel M E n) (a : M)
    (e v : E) (q q' : BlockState n E) :
    ‖P.stressResponse a e v q - P.stressResponse a e v q'‖ ≤
      Real.sqrt n * ‖q - q'‖ := by
  rw [PronyModel.stressResponse, PronyModel.stressResponse,
    add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k : Fin n, (q k - q' k)‖ ≤ ∑ k : Fin n, ‖q k - q' k‖ := norm_sum_le _ _
    _ ≤ Real.sqrt n * Real.sqrt (∑ k : Fin n, ‖q k - q' k‖ ^ 2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin n => (1 : ℝ))
        (fun k => ‖q k - q' k‖)
    _ = Real.sqrt n * ‖q - q'‖ := by
      rw [PiLp.norm_eq_of_L2]
      simp only [PiLp.sub_apply]

/-- Proposition B.13 (`eq:ua_err`), stress estimate: summing `n` tensor
blocks introduces precisely the factor `√n`. -/
theorem stress_error_le {n : ℕ} (P : PronyModel M E n) (a : M)
    {e v : E} {q qIV : BlockState n E} {σ : E} {εF εG rateLower : ℝ}
    (hF : ‖σ - P.stressResponse a e v q‖ ≤ εF)
    (hState : ‖q - qIV‖ ≤ εG / rateLower) :
    ‖σ - P.stressResponse a e v qIV‖ ≤ εF + Real.sqrt n * εG / rateLower := by
  calc
    _ ≤ ‖σ - P.stressResponse a e v q‖ +
        ‖P.stressResponse a e v q - P.stressResponse a e v qIV‖ := by
      simpa only [dist_eq_norm] using
        dist_triangle σ (P.stressResponse a e v q) (P.stressResponse a e v qIV)
    _ ≤ εF + Real.sqrt n * ‖q - qIV‖ :=
      add_le_add hF (prony_stress_lipschitz P a e v q qIV)
    _ ≤ εF + Real.sqrt n * (εG / rateLower) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hState (Real.sqrt_nonneg _)) _
    _ = _ := by rw [mul_div_assoc]

end KVApproximation.Dynamics
