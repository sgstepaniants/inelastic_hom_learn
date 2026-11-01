module

public import KVApproximation.NeuralOperators.FourierMapping

/-!
# Fourier layers as Lipschitz maps on L²
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remark 4.3, affine stage: local channel weights,
finite Fourier synthesis and the stated constant bias define an actual affine L² map. -/
theorem FourierLayer.exists_affineCLM {d input output : ℕ}
    (L : FourierLayer d input output) :
    ∃ A : ChannelField d input →L[ℝ] ChannelField d output,
      ∃ b : ChannelField d output, ∀ h : ChannelField d input,
        ((A h + b : ChannelField d output) : PeriodicCell d → Channels output) =ᵐ[cellMeasure d]
          fun y => WithLp.toLp 2 (fun i =>
            (∑ j : Fin input, L.localWeight i j * h y j) +
              (L.fourierPart h y i).re + L.bias i) := by
  sorry

/-- Example 2.1 and Remark 4.3: a Fourier layer with globally Lipschitz
activation induces a globally Lipschitz map of the actual Euclidean L² spaces. -/
theorem FourierLayer.exists_lipschitz_evalLp {d input output : ℕ}
    (L : FourierLayer d input output) {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) :
    ∃ K' : NNReal, ∃ F : ChannelField d input → ChannelField d output,
      LipschitzWith K' F ∧ ∀ h : ChannelField d input,
        (F h : PeriodicCell d → Channels output) =ᵐ[cellMeasure d] L.eval σ h := by
  sorry

/-- Example 2.1 and Remark 4.3: every finite chain induces a globally
Lipschitz map of L² with the prescribed representative evaluation. -/
theorem FourierChain.exists_lipschitz_evalLp {d input output : ℕ}
    (L : FourierChain d input output) {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) :
    ∃ K' : NNReal, ∃ F : ChannelField d input → ChannelField d output,
      LipschitzWith K' F ∧ ∀ h : ChannelField d input,
        (F h : PeriodicCell d → Channels output) =ᵐ[cellMeasure d] L.eval σ h := by
  sorry

end KVApproximation.NeuralOperators
