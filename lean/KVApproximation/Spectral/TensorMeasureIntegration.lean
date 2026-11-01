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
  let : IsFiniteMeasure ν.variation := ⟨hfinite⟩
  have hrestrict : ν.variation.restrict (Set.Icc a b) = ν.variation :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport)
  have hi := hf.integrableOn_Icc (μ := ν.variation)
  rwa [IntegrableOn, hrestrict] at hi

/-- Lemma B.5, polynomial approximation step: the integral difference is
controlled by the uniform test error and the full Frobenius variation. -/
theorem dist_tensorIntegral_le_of_bound (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ r ∈ Set.Icc a b, |f r - g r| ≤ M) :
    dist (tensorIntegral ν f) (tensorIntegral ν g) ≤
      M * (totalVariation ν Set.univ).toReal := by
  -- Expose the inherited submodule instances for the iterated operator norm.
  let : NormedAddCommGroup (Tensor.Elasticity d) :=
    (Tensor.elasticitySubmodule d).normedAddCommGroup
  let : NormedSpace ℝ (Tensor.Elasticity d) :=
    (Tensor.elasticitySubmodule d).normedSpace
  let : IsFiniteMeasure ν.variation := ⟨hfinite⟩
  have hfi := ν.integrable_continuousOn hfinite hsupport f hf
  have hgi := ν.integrable_continuousOn hfinite hsupport g hg
  rw [dist_eq_norm, tensorIntegral, tensorIntegral,
    ← VectorMeasure.integral_sub hfi hgi]
  have hAE : ∀ᵐ r ∂ν.variation, ‖(f - g) r‖ ≤ M := by
    filter_upwards [ae_iff.mpr hsupport] with r hr
    exact hbound r hr
  have hi := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := ν) (B := ContinuousLinearMap.lsmul ℝ ℝ (E := Tensor.Elasticity d)) hAE
  apply hi.trans
  change M * ‖ContinuousLinearMap.lsmul ℝ ℝ (E := Tensor.Elasticity d)‖ *
    (ν.variation Set.univ).toReal ≤ M * (ν.variation Set.univ).toReal
  calc
    _ ≤ M * 1 * (ν.variation Set.univ).toReal := by
      gcongr
      exact ContinuousLinearMap.opNorm_lsmul_le
    _ = _ := by rw [mul_one]

end KVApproximation.Spectral
