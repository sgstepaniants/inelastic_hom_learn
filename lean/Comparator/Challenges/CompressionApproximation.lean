module

public import KVApproximation.Spectral.Compression

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.OperatorTheory KVApproximation.Tensor

namespace KVApproximation.Spectral

/-- Lemma B.5 (`eq:weak_converge_decomposed`): each continuous-test
remainder has the paper's dimension-independent mismatch-energy bound. -/
theorem compressedMeasure_pairing_sub_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {d : ℕ} (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
    (hν : IsCompressedMeasure V E X ι ν)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (αE / βV) (βE / αV)))
    (hg : ContinuousOn g (Set.Icc (αE / βV) (βE / αV)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ r ∈ Set.Icc (αE / βV) (βE / αV), |f r - g r| ≤ ε)
    (e k : Symmetric d) :
    |⟪e, action (tensorIntegral ν f) k⟫_ℝ -
      ⟪e, action (tensorIntegral ν g) k⟫_ℝ| ≤
      ε * (βV * βE / αE) * ‖ι e‖ * ‖ι k‖ := by
  sorry

end KVApproximation.Spectral
