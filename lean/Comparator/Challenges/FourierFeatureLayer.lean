module

public import KVApproximation.NeuralOperators.FourierMapping

/-!
# Finite observations realized by a Fourier layer
-/

public section

open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, finite-feature realization: one actual Fourier layer with
zero local matrix and constant bias realizes every finite real linear
combination of scalar Fourier observations at the spatial origin. -/
theorem exists_fourier_feature_layer {d input features output : ℕ}
    (P : Fin features → FourierProjection d input 1)
    (w : Matrix (Fin output) (Fin features) ℝ) (b : Fin output → ℝ) :
    ∃ L : FourierLayer d input output,
      L.localWeight = 0 ∧ L.bias = b ∧
        ∀ (h : PeriodicCell d → Channels input) (j : Fin output),
          (L.fourierPart h 0 j).re = ∑ i : Fin features, w j i * (P i).eval h 0 := by
  sorry

/-- Remark 4.3, continuous hidden fields: with zero local matrix, a finite
Fourier layer is jointly continuous in its L² input and spatial point for
every continuous activation. -/
theorem FourierLayer.continuous_eval_of_zero_localWeight {d input output : ℕ}
    (L : FourierLayer d input output) (hL : L.localWeight = 0)
    {σ : ℝ → ℝ} (hσ : Continuous σ) :
    Continuous (fun p : ChannelField d input × PeriodicCell d => L.eval σ p.1 p.2) := by
  sorry

end KVApproximation.NeuralOperators
