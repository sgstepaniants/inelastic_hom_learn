module

public import KVApproximation.NeuralOperators.FourierMapping

public section

noncomputable section

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, Fourier features: paired opposite-frequency weights realize
the real part of any complex multiple of a single channel coefficient. -/
theorem exists_scalarFourierProjection {d n : ℕ}
    (k : Fin d → ℤ) (j : Fin n) (z : ℂ) :
    ∃ P : FourierProjection d n 1, ∀ h : ChannelField d n,
      P.eval h 0 = (z * channelFourier h k j).re := by
  sorry

/-- Remark 4.3, separation: all scalar projections in the actual finite
conjugate-symmetric architecture determine the L² channel field. -/
theorem eq_of_scalarFourierProjections_eq {d n : ℕ} {h g : ChannelField d n}
    (heq : ∀ P : FourierProjection d n 1, P.eval h 0 = P.eval g 0) : h = g := by
  sorry

end KVApproximation.NeuralOperators
