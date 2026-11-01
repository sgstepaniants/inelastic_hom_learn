module

public import KVApproximation.Spectral.TensorMeasure
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Continuous tests on the spectral interval
-/

public section

open MeasureTheory

namespace KVApproximation.Spectral

variable {d : ℕ} {a b : ℝ} (ν : TensorMeasure d)
  (hfinite : totalVariation ν Set.univ < ⊤)
  (hsupport : ν.SupportedOn (Set.Icc a b))

include hfinite hsupport

/-- Lemma B.5: continuity on the supported interval suffices for integrability
against the tensor measure's Frobenius variation. -/
theorem TensorMeasure.integrable_continuousOn (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) : Integrable f ν.variation := by
  sorry

/-- Lemma B.5, polynomial approximation step: the integral difference is
controlled by the uniform test error and the full Frobenius variation. -/
theorem dist_tensorIntegral_le_of_bound (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ r ∈ Set.Icc a b, |f r - g r| ≤ M) :
    dist (tensorIntegral ν f) (tensorIntegral ν g) ≤
      M * (totalVariation ν Set.univ).toReal := by
  sorry

end KVApproximation.Spectral
