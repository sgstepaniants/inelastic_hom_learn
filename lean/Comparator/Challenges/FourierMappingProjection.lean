module

public import KVApproximation.NeuralOperators.FourierMapping

/-!
# Bounded linear Fourier projection
-/

public section

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remark 4.3: the finite Fourier projection defines an
actual continuous real-linear map on Euclidean L² channel fields. -/
theorem FourierProjection.exists_evalCLM {d input output : ℕ}
    (P : FourierProjection d input output) :
    ∃ A : ChannelField d input →L[ℝ] Channels output,
      ∀ h : ChannelField d input, A h = P.eval h := by
  sorry

end KVApproximation.NeuralOperators
