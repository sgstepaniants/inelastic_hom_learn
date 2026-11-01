module

public import KVApproximation.Spectral.TensorMeasureIntegration
public import KVApproximation.Analysis.PositiveScalarization
public import KVApproximation.Analysis.VectorMeasureDensity
public import KVApproximation.Tensor.FormRepresentation
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Positive weighting of spectral measures
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Tensor KVApproximation.Analysis

namespace KVApproximation.Spectral

/-- Lemma B.6 (`eq:weighted_measure_def`): the resolvent weight is
integrable against variation and defines a positive measure supported on the same interval. -/
theorem weightedMeasure_properties {d : ℕ} {lower upper c : ℝ}
    (hlower : 0 < lower) (hc : 0 < c) (ν : TensorMeasure d)
    (hνpos : ν.Positive) (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation ν Set.univ < ⊤) :
    Integrable (resolventWeight c) ν.variation ∧
      (weightedMeasure c ν).Positive ∧
      (weightedMeasure c ν).SupportedOn (Set.Icc lower upper) ∧
      totalVariation (weightedMeasure c ν) Set.univ ≤ totalVariation ν Set.univ := by
  have hwcont : ContinuousOn (resolventWeight c) (Set.Icc lower upper) :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun r hr => (add_pos hc (hlower.trans_le hr.1)).ne')
  have hwbound (r : ℝ) (hr : r ∈ Set.Icc lower upper) :
      0 ≤ resolventWeight c r ∧ resolventWeight c r ≤ 1 := by
    have hrpos := hlower.trans_le hr.1
    constructor
    · exact (div_pos hrpos (add_pos hc hrpos)).le
    · exact (div_le_one (add_pos hc hrpos)).2 (by linarith)
  have hνw := ν.integrable_continuousOn hνfinite hνsupport (resolventWeight c) hwcont
  have hvar : (weightedMeasure c ν).variation ≤ ν.variation := by
    have h := VectorMeasure.variation_WithDensity_le
      (μ := ν) (f := resolventWeight c) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    simp only [VectorMeasure.variation_transpose_lsmul] at h
    apply h.trans
    calc
      _ ≤ ν.variation.withDensity (fun _ => 1) := by
        apply withDensity_mono
        filter_upwards [ae_iff.mpr hνsupport] with r hr
        rw [Real.enorm_eq_ofReal (hwbound r hr).1, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (hwbound r hr).2
      _ = ν.variation := by rw [withDensity_const, one_smul]
  refine ⟨hνw, ?_, ?_, hvar Set.univ⟩
  · intro B hB e
    let φ : Elasticity d →L[ℝ] ℝ := (innerSL ℝ e).comp ((actionL d).flip e)
    obtain ⟨μ, hfinite, hreal, hnull⟩ :=
      exists_finite_positive_scalarization ν φ (fun s hs => hνpos s hs e)
    let := hfinite
    have hsupport : μ (Set.Icc lower upper)ᶜ = 0 :=
      hnull _ measurableSet_Icc.compl hνsupport
    have hμw : Integrable (resolventWeight c) μ := by
      have hi := hwcont.integrableOn_Icc (μ := μ)
      rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport)] at hi
    change 0 ≤ φ (ν.withDensity (resolventWeight c) (ContinuousLinearMap.lsmul ℝ ℝ) B)
    rw [scalarization_withDensity_apply ν φ μ (fun s hs => (hreal s hs).symm)
      (resolventWeight c) hνw hμw B hB]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae (ae_iff.mpr hsupport)] with r hr
    exact (hwbound r hr).1
  · exact le_antisymm ((hvar _).trans_eq hνsupport) bot_le

/-- Lemma B.6, weak-continuity bridge: testing the weighted measure is
equivalent to multiplying the continuous test by the resolvent weight. -/
theorem weightedMeasure_integral {d : ℕ} {lower upper c : ℝ}
    (hlower : 0 < lower) (hc : 0 < c) (ν : TensorMeasure d)
    (hνpos : ν.Positive) (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc lower upper)) :
    Integrable f (weightedMeasure c ν).variation ∧
      tensorIntegral (weightedMeasure c ν) f =
        tensorIntegral ν (fun r => f r * resolventWeight c r) := by
  obtain ⟨hνw, _, hsupport, hvar⟩ :=
    weightedMeasure_properties hlower hc ν hνpos hνsupport hνfinite
  have hfinite := hvar.trans_lt hνfinite
  have hfi := (weightedMeasure c ν).integrable_continuousOn hfinite hsupport f hf
  have hwcont : ContinuousOn (resolventWeight c) (Set.Icc lower upper) :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun r hr => (add_pos hc (hlower.trans_le hr.1)).ne')
  have hwpos (r : ℝ) (hr : r ∈ Set.Icc lower upper) : 0 ≤ resolventWeight c r :=
    (div_pos (hlower.trans_le hr.1) (add_pos hc (hlower.trans_le hr.1))).le
  have hwmeas : Measurable (resolventWeight c) :=
    measurable_id.div (measurable_const.add measurable_id)
  have hdmeas : Measurable (fun r => ENNReal.ofReal (resolventWeight c r)) :=
    hwmeas.ennreal_ofReal
  have hνfw := ν.integrable_continuousOn hνfinite hνsupport
    (fun r => f r * resolventWeight c r) (hf.mul hwcont)
  refine ⟨hfi, ?_⟩
  have hdiag (e : Symmetric d) :
      ⟪e, action (tensorIntegral (weightedMeasure c ν) f) e⟫_ℝ =
        ⟪e, action (tensorIntegral ν (fun r => f r * resolventWeight c r)) e⟫_ℝ := by
    let φ : Elasticity d →L[ℝ] ℝ := (innerSL ℝ e).comp ((actionL d).flip e)
    obtain ⟨μ, hμfinite, hreal, hnull⟩ :=
      exists_finite_positive_scalarization ν φ (fun s hs => hνpos s hs e)
    let := hμfinite
    have hμsupport : μ (Set.Icc lower upper)ᶜ = 0 :=
      hnull _ measurableSet_Icc.compl hνsupport
    have hiμ (q : ℝ → ℝ) (hq : ContinuousOn q (Set.Icc lower upper)) : Integrable q μ := by
      have hi := hq.integrableOn_Icc (μ := μ)
      rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμsupport)] at hi
    have hμw := hiμ (resolventWeight c) hwcont
    let ρ := μ.withDensity (fun r => ENNReal.ofReal (resolventWeight c r))
    let : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_ofReal hμw.2
    have hρsupport : ρ (Set.Icc lower upper)ᶜ = 0 :=
      withDensity_absolutelyContinuous μ _ hμsupport
    have hρf : Integrable f ρ := by
      have hi := hf.integrableOn_Icc (μ := ρ)
      rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hρsupport)] at hi
    have hρscalar (s : Set ℝ) (hs : MeasurableSet s) :
        φ (weightedMeasure c ν s) = ρ.real s := by
      have hρreal := withDensity_real_apply_eq_integral
        (μ := μ) (f := fun r => ENNReal.ofReal (resolventWeight c r))
        hdmeas.aemeasurable (Filter.Eventually.of_forall (fun _ _ => ENNReal.ofReal_lt_top))
        hs.nullMeasurableSet
      change φ (ν.withDensity (resolventWeight c) (ContinuousLinearMap.lsmul ℝ ℝ) s) = _
      rw [scalarization_withDensity_apply ν φ μ (fun B hB => (hreal B hB).symm)
        (resolventWeight c) hνw hμw s hs]
      rw [hρreal]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_iff.mpr hμsupport)] with r hr
      exact (ENNReal.toReal_ofReal (hwpos r hr)).symm
    change φ (VectorMeasure.integral (weightedMeasure c ν) f _) =
      φ (VectorMeasure.integral ν (fun r => f r * resolventWeight c r) _)
    rw [integral_scalarization (weightedMeasure c ν) φ ρ hρscalar f hfi hρf,
      integral_scalarization ν φ μ (fun B hB => (hreal B hB).symm)
        (fun r => f r * resolventWeight c r) hνfw (hiμ _ (hf.mul hwcont))]
    change (∫ r, f r ∂μ.withDensity (fun r => ENNReal.ofReal (resolventWeight c r))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hdmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f]
    apply integral_congr_ae
    filter_upwards [ae_iff.mpr hμsupport] with r hr
    rw [ENNReal.toReal_ofReal (hwpos r hr), smul_eq_mul, mul_comm]
  let A := tensorIntegral (weightedMeasure c ν) f
  let B := tensorIntegral ν (fun r => f r * resolventWeight c r)
  let Q (T : Elasticity d) : LinearMap.BilinForm ℝ (Symmetric d) :=
    ((innerSL ℝ).comp (actionL d T)).toLinearMap₁₂
  have hsymm (T : Elasticity d) : (Q T).IsSymm := ⟨fun e g => by
    change ⟪action T e, g⟫_ℝ = ⟪action T g, e⟫_ℝ
    rw [action_symmetric, real_inner_comm]⟩
  have hQ : Q A = Q B :=
    LinearMap.BilinForm.ext_of_isSymm (hsymm A) (hsymm B) fun e => by
      change ⟪action A e, e⟫_ℝ = ⟪action B e, e⟫_ℝ
      simpa only [action_symmetric] using hdiag e
  apply eq_of_inner_action_eq
  intro e g
  have heq := congrArg (fun q : LinearMap.BilinForm ℝ (Symmetric d) => q e g) hQ
  change ⟪action A e, g⟫_ℝ = ⟪action B e, g⟫_ℝ at heq
  simpa only [action_symmetric] using heq

end KVApproximation.Spectral
