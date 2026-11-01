module

public import KVApproximation.Homogenization.CellSpectralMeasure
public import KVApproximation.Homogenization.CellTensorBounds
public import KVApproximation.OperatorTheory.CellResolvent
public import KVApproximation.OperatorTheory.CoerciveCombinationBounds
public import KVApproximation.Spectral.WeightedMeasureIntegration
public import KVApproximation.Spectral.TensorVariation
public import KVApproximation.Tensor.Dimensions
public import Mathlib.Tactic.FieldSimp

/-!
# The sharp weighted spectral mass bound

The transformed cell equation and the static variational bounds control each
quadratic pairing. Positivity then bounds Frobenius variation by the trace.
-/

public section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Homogenization KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Spectral

/-- Lemma B.6, quantitative estimate preceding `eq:weighted_measure_mass`:
one common bound holds before taking any supremum over materials. -/
theorem weightedMeasure_variation_le {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
    (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field)
    (ν : TensorMeasure d)
    (hν : IsSpectralRepresentation ν C.kernel (lowerRate αE βV) (upperRate βE αV)) :
    totalVariation (weightedMeasure (βE / βV) ν) Set.univ ≤
      ENNReal.ofReal (weightedVariationBound (strainDimension d) αV βV αE βE) := by
  classical
  have hβV := hαV.trans_le hVorder
  have hβE := hαE.trans_le hEorder
  let s := βE / βV
  have hs : 0 < s := div_pos hβE hβV
  let A := V.toForm.addScaled E.toForm s⁻¹ (inv_nonneg.mpr hs.le)
  have hV' : V.toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hV u
  have hE' : E.toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hE u
  have hA : A.HasBounds (αV + s⁻¹ * αE) (βV + s⁻¹ * βE) :=
    V.toForm.addScaled_bounds E.toForm s⁻¹ (inv_nonneg.mpr hs.le) hV' hE'
  have hAform (u v) : A.form u v = V.toForm.form u v + s⁻¹ * E.toForm.form u v := rfl
  have hcompressed := cell_spectral_measure_isCompressed V E C hαV hβV hαE hβE hV hE ν hν
  have hwcont : ContinuousOn (resolventWeight s) (Set.Icc (αE / βV) (βE / αV)) :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun r hr => (add_pos hs ((div_pos hαE hβV).trans_le hr.1)).ne')
  have hμpos := (weightedMeasure_properties (div_pos hαE hβV) hs ν
    hν.1 hν.2.1 hν.2.2.1).2.1
  have hpair (e : Symmetric d) :
      ⟪e, action (weightedMeasure s ν Set.univ) e⟫_ℝ =
        A.homogenizedForm (correctorSubspace d) (constantStrainL d) e e -
        V.toForm.homogenizedForm (correctorSubspace d) (constantStrainL d) e e -
        s⁻¹ * E.toForm.homogenizedForm (correctorSubspace d) (constantStrainL d) e e := by
    rw [weightedMeasure, VectorMeasure.withDensity_apply_univ]
    change ⟪e, action (tensorIntegral ν (resolventWeight s)) e⟫_ℝ = _
    rw [(compressedMeasure_integral V.toForm E.toForm (correctorSubspace d)
      (constantStrainL d) ν hcompressed hαV hβV hαE hβE hV' hE'
      (resolventWeight s) hwcont).2 e e]
    exact homogenizedForm_resolvent V.toForm E.toForm A (correctorSubspace d)
      (constantStrainL d) s hs hAform hαV hβV hαE hβE hV' hE' e e
  have hquad (e : Symmetric d) :
      ⟪e, action (weightedMeasure s ν Set.univ) e⟫_ℝ ≤
        (2 * βV - αV - βV * αE / βE) * ‖e‖ ^ 2 := by
    have hAb := A.homogenizedForm_bounds (correctorSubspace d) (constantStrainL d)
      norm_constantStrain constantStrain_orthogonal_corrector
      (add_nonneg hαV.le (mul_nonneg (inv_nonneg.mpr hs.le) hαE.le)) hA e
    have hVb := V.toForm.homogenizedForm_bounds (correctorSubspace d) (constantStrainL d)
      norm_constantStrain constantStrain_orthogonal_corrector hαV.le hV' e
    have hEb := E.toForm.homogenizedForm_bounds (correctorSubspace d) (constantStrainL d)
      norm_constantStrain constantStrain_orthogonal_corrector hαE.le hE' e
    rw [hpair]
    calc
      _ ≤ (βV + s⁻¹ * βE) * ‖e‖ ^ 2 - αV * ‖e‖ ^ 2 -
          s⁻¹ * (αE * ‖e‖ ^ 2) :=
        sub_le_sub (sub_le_sub hAb.2 hVb.1)
          (mul_le_mul_of_nonneg_left hEb.1 (inv_nonneg.mpr hs.le))
      _ = _ := by
        dsimp [s]
        field_simp
        ring
  let b := stdOrthonormalBasis ℝ (Symmetric d)
  have htrace : tensorTrace (weightedMeasure s ν Set.univ) ≤
      weightedVariationBound (strainDimension d) αV βV αE βE := by
    rw [tensorTrace_eq_sum b]
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (Symmetric d)),
          (2 * βV - αV - βV * αE / βE) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [b.norm_eq_one, one_pow, mul_one] using hquad (b i)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          finrank_symmetric, weightedVariationBound]
  exact ((weightedMeasure s ν).variation_le_trace hμpos MeasurableSet.univ).trans
    (ENNReal.ofReal_le_ofReal htrace)

end KVApproximation.Spectral
