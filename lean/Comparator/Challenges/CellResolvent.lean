module

public import KVApproximation.OperatorTheory.SpectralBounds

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

/-- Theorem 3.1, transformed cell identity, and Lemma B.6: the resolvent
compression is the difference between the combined effective form and the
two separate effective forms. -/
theorem homogenizedForm_resolvent
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E A : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H)
    (s : ℝ) (hs : 0 < s)
    (hA : ∀ u v, A.form u v = V.form u v + s⁻¹ * E.form u v)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) (e g : F) :
    ⟪cfc (fun r => r / (s + r)) (weightedRelaxation V E X)
        (weightedMismatch V E X ι e), weightedMismatch V E X ι g⟫_ℝ =
      A.homogenizedForm X ι e g - V.homogenizedForm X ι e g -
        s⁻¹ * E.homogenizedForm X ι e g := by
  sorry

end KVApproximation.OperatorTheory
