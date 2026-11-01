module

public import KVApproximation.NeuralOperators.FourierMappingAffine
public import KVApproximation.NeuralOperators.FourierMappingRepresentatives
public import KVApproximation.Analysis.Nemytskii

/-!
# Lipschitz Fourier layers and chains
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1, activation ingredient: coordinatewise activation preserves
the scalar Lipschitz constant in the Euclidean channel norm. -/
private theorem lipschitz_channels {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) (n : ℕ) :
    LipschitzWith K (fun x : Channels n => WithLp.toLp 2 (fun i => σ (x i))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg K.coe_nonneg dist_nonneg)).mp
  rw [PiLp.dist_sq_eq_of_L2, mul_pow, PiLp.dist_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change dist (σ (x i)) (σ (y i)) ^ 2 ≤ (K : ℝ) ^ 2 * dist (x i) (y i) ^ 2
  simpa only [mul_pow] using
    pow_le_pow_left₀ dist_nonneg (hσ.dist_le_mul (x i) (y i)) 2

/-- Example 2.1 and Remark 4.3: a Fourier layer with globally Lipschitz
activation induces a globally Lipschitz map of the actual Euclidean L² spaces. -/
theorem FourierLayer.exists_lipschitz_evalLp {d input output : ℕ}
    (L : FourierLayer d input output) {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) :
    ∃ K' : NNReal, ∃ F : ChannelField d input → ChannelField d output,
      LipschitzWith K' F ∧ ∀ h : ChannelField d input,
        (F h : PeriodicCell d → Channels output) =ᵐ[cellMeasure d] L.eval σ h := by
  obtain ⟨A, b, hA⟩ := L.exists_affineCLM
  obtain ⟨N, hN, hNrep⟩ := exists_lipschitz_compositionLp (cellMeasure d) 2
    (lipschitz_channels hσ output)
  have haffine : LipschitzWith ‖A‖₊ (fun h => A h + b) := by
    apply LipschitzWith.of_dist_le_mul
    intro h g
    simpa only [dist_add_right] using A.lipschitzWith.dist_le_mul h g
  refine ⟨K * ‖A‖₊, fun h => N (A h + b), hN.comp haffine, ?_⟩
  intro h
  filter_upwards [hNrep (A h + b), hA h] with y hN hA
  rw [hN, hA]
  rfl

/-- Example 2.1 and Remark 4.3: every finite chain induces a globally
Lipschitz map of L² with the prescribed representative evaluation. -/
theorem FourierChain.exists_lipschitz_evalLp {d input output : ℕ}
    (L : FourierChain d input output) {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) :
    ∃ K' : NNReal, ∃ F : ChannelField d input → ChannelField d output,
      LipschitzWith K' F ∧ ∀ h : ChannelField d input,
        (F h : PeriodicCell d → Channels output) =ᵐ[cellMeasure d] L.eval σ h := by
  induction L with
  | nil width => exact ⟨1, id, LipschitzWith.id, fun _ => Filter.EventuallyEq.rfl⟩
  | cons L rest ih =>
      obtain ⟨K₁, F, hF, hFrep⟩ := L.exists_lipschitz_evalLp hσ
      obtain ⟨K₂, G, hG, hGrep⟩ := ih
      refine ⟨K₂ * K₁, G ∘ F, hG.comp hF, ?_⟩
      intro h
      exact (hGrep (F h)).trans (rest.eval_congr_ae σ (hFrep h))

end KVApproximation.NeuralOperators
