module

public import KVApproximation.NeuralOperators.FourierMapping

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, finite Fourier observation: a real L² averaging kernel can
be approximated in operator norm by an actual conjugate-symmetric projection. -/
theorem exists_fourierProjection_approx_integral
    {d n : ℕ} (κ : Lp ℝ 2 (cellMeasure d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : FourierProjection d n n, ∀ h : ChannelField d n,
      ‖P.eval h - ∫ y, κ y • h y ∂cellMeasure d‖ ≤ ε * ‖h‖ := by
  sorry

end KVApproximation.NeuralOperators
