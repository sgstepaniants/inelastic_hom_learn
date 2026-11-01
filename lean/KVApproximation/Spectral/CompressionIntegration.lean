module

public import KVApproximation.Spectral.CompressionConstruction
public import KVApproximation.Tensor.LinearActionIdentities
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Continuous tests of the relaxation measure

Interval support gives integrability against Frobenius variation. Diagonal
tests reduce to the positive scalar spectral measures; real polarization then
recovers all tensor pairings.
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.OperatorTheory KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {d : ℕ} (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
  (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
  (hν : IsCompressedMeasure V E X ι ν)
  {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
  (hαE : 0 < αE) (hβE : 0 < βE)
  (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE)

include hν hαV hβV hαE hβE hV hE

/-- Appendix A.2 and Lemma B.5: continuous test functions commute with
compression of the weighted continuous functional calculus. -/
theorem compressedMeasure_integral (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (αE / βV) (βE / αV))) :
    Integrable f ν.variation ∧ ∀ e g : Symmetric d,
      ⟪e, action (tensorIntegral ν f) g⟫_ℝ =
        ⟪cfc f (weightedRelaxation V E X) (weightedMismatch V E X ι e),
          weightedMismatch V E X ι g⟫_ℝ := by
  obtain ⟨hsupport, hfinite⟩ :=
    compressedMeasure_supported V E X ι ν hν hαV hβV hαE hβE hV hE
  let : IsFiniteMeasure ν.variation := ⟨hfinite⟩
  have hrestrict : ν.variation.restrict (Set.Icc (αE / βV) (βE / αV)) =
      ν.variation := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport)
  have hνf : Integrable f ν.variation := by
    have h := hf.integrableOn_Icc (μ := ν.variation)
    rwa [IntegrableOn, hrestrict] at h
  have hR := weightedRelaxation_isSelfAdjoint V E X
  have hfR : ContinuousOn f (spectrum ℝ (weightedRelaxation V E X)) := by
    apply hf.mono
    rw [weightedRelaxation_spectrum_eq]
    exact relaxation_spectrum_subset V E X hαV hβV hαE hβE hV hE
  have hdiag (e : Symmetric d) :
      ⟪e, action (tensorIntegral ν f) e⟫_ℝ =
        ⟪cfc f (weightedRelaxation V E X) (weightedMismatch V E X ι e),
          weightedMismatch V E X ι e⟫_ℝ := by
    obtain ⟨hPf, hcalc⟩ := boundedPVM_integral
      (ContinuousLinearMap.isSelfAdjoint_complexifyL2_iff.mpr hR)
      (weightedRelaxation_complex_spectrum_subset V E X hαV hβV hαE hβE hV hE)
      f hf (complexMismatch V E X ι e)
    rw [pvmCompression_integral_diag (relaxationPVM V E X)
      (complexMismatch V E X ι) ν hν f e hνf hPf, relaxationPVM, hcalc]
    rw [← ContinuousLinearMap.complexifyL2_cfc f (weightedRelaxation V E X) hfR hR]
    simp only [complexMismatch, ContinuousLinearMap.complexifyL2_toLp_ofReal,
      WithLp.complexification_re_inner,
      TauCeti.Complexification.ofReal_re, TauCeti.Complexification.ofReal_im,
      inner_zero_left, add_zero]
    exact real_inner_comm _ _
  let B : LinearMap.BilinForm ℝ (Symmetric d) :=
    ((innerSL ℝ).comp (actionL d (tensorIntegral ν f))).toLinearMap₁₂
  let C : LinearMap.BilinForm ℝ (Symmetric d) :=
    ((innerSL ℝ).bilinearComp
      ((cfc f (weightedRelaxation V E X)).comp (weightedMismatch V E X ι))
      (weightedMismatch V E X ι)).toLinearMap₁₂
  have hB : B.IsSymm := ⟨fun e g => by
    change ⟪action (tensorIntegral ν f) e, g⟫_ℝ =
      ⟪action (tensorIntegral ν f) g, e⟫_ℝ
    rw [action_symmetric, real_inner_comm]⟩
  have hC : C.IsSymm := ⟨fun e g => by
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (IsSelfAdjoint.cfc (f := f) (a := weightedRelaxation V E X)))
      (weightedMismatch V E X ι e) (weightedMismatch V E X ι g)).trans
      (real_inner_comm _ _)⟩
  have hBC : B = C := LinearMap.BilinForm.ext_of_isSymm hB hC fun e => by
    change ⟪action (tensorIntegral ν f) e, e⟫_ℝ = _
    rw [action_symmetric]
    exact hdiag e
  refine ⟨hνf, fun e g => ?_⟩
  calc
    _ = B e g := (action_symmetric _ _ _).symm
    _ = C e g := congrArg (fun Q : LinearMap.BilinForm ℝ (Symmetric d) => Q e g) hBC
    _ = _ := rfl

end KVApproximation.Spectral
