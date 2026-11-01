module

public import KVApproximation.Homogenization.ConstantStrainIdentities
public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Spectral.CompressionMoments
public import KVApproximation.Spectral.Bounds
public import KVApproximation.Tensor.Dimensions

/-!
# Spectral representation of the periodic cell memory

Appendix A.2 compresses the weighted relaxation PVM through the cell mismatch.
The variation estimate sums the mismatch energy over an orthonormal strain
basis; normalized cell volume and the exact strain dimension preserve the
paper's constant.
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Homogenization
open KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Spectral

/-- Proposition 3.3 (`prop:spectral_rep`): a positive tensor measure
represents the actual cell memory kernel, with the stated spectral support
and Frobenius total-variation bound. -/
theorem spectral_representation {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field) :
    ∃ ν : TensorMeasure d,
      ν.Positive ∧
      ν.SupportedOn (Set.Icc (lowerRate αE βV) (upperRate βE αV)) ∧
      totalVariation ν Set.univ ≤
        ENNReal.ofReal (spectralVariationBound (strainDimension d) βV βE αE) ∧
      ∀ t : ℝ, 0 ≤ t →
        C.kernel t = tensorIntegral ν (fun r => r * Real.exp (-r * t)) := by
  have hV' : V.toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hV u
  have hE' : E.toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hE u
  let X := correctorSubspace d
  let ι := constantStrainL d
  obtain ⟨ν, hν, _⟩ := compressedMeasure_exists_unique V.toForm E.toForm X ι
  let b := stdOrthonormalBasis ℝ (Symmetric d)
  obtain ⟨hpos, _, hvar⟩ := compressedMeasure_positive_trace V.toForm E.toForm X ι ν hν b
  have hsupport := (compressedMeasure_supported V.toForm E.toForm X ι ν hν
    hαV hβV hαE hβE hV' hE').1
  have hmismatch (i : Fin (Module.finrank ℝ (Symmetric d))) :
      ‖weightedMismatch V.toForm E.toForm X ι (b i)‖ ^ 2 ≤ βV * βE / αE := by
    rw [← real_inner_self_eq_norm_sq (weightedMismatch V.toForm E.toForm X ι (b i))]
    change V.toForm.form (mismatch V.toForm E.toForm X (ι (b i)))
      (mismatch V.toForm E.toForm X (ι (b i))) ≤ _
    have h := mismatch_energy_le V.toForm E.toForm X hαE hβV.le hV' hE' (ι (b i))
    simpa only [ι, norm_constantStrain, b.norm_eq_one, one_pow, mul_one] using h
  have hsum : (∑ i, ‖weightedMismatch V.toForm E.toForm X ι (b i)‖ ^ 2) ≤
      spectralVariationBound (strainDimension d) βV βE αE := by
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (Symmetric d)), βV * βE / αE :=
        Finset.sum_le_sum fun i _ => hmismatch i
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          finrank_symmetric, spectralVariationBound]
        ring
  refine ⟨ν, hpos, hsupport, hvar.trans (ENNReal.ofReal_le_ofReal hsum), ?_⟩
  intro t ht
  apply eq_of_inner_action_eq
  intro e g
  rw [C.kernel_eq]
  exact (compressedMeasure_memory V.toForm E.toForm X ι ν hν
    hαV hβV hαE hβE hV' hE' t ht e g).symm

end KVApproximation.Spectral
