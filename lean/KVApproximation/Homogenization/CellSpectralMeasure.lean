module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Spectral.CompressionMoments
public import KVApproximation.Spectral.RepresentationUniqueness
public import KVApproximation.Spectral.Bounds

/-!
# Identification of the cell spectral measure
-/

public section

open KVApproximation.Tensor KVApproximation.Homogenization
open scoped InnerProductSpace

namespace KVApproximation.Spectral

/-- Proposition 3.3 and Lemma B.5: a spectral representation of the actual
cell kernel is the compression of the cell relaxation PVM. -/
theorem cell_spectral_measure_isCompressed {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field)
    (ν : TensorMeasure d)
    (hν : IsSpectralRepresentation ν C.kernel (lowerRate αE βV) (upperRate βE αV)) :
    IsCompressedMeasure V.toForm E.toForm (correctorSubspace d) (constantStrainL d) ν := by
  have hV' : V.toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hV u
  have hE' : E.toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hE u
  obtain ⟨μ, hμ, _⟩ := compressedMeasure_exists_unique
    V.toForm E.toForm (correctorSubspace d) (constantStrainL d)
  obtain ⟨hsupport, hfinite⟩ := compressedMeasure_supported
    V.toForm E.toForm (correctorSubspace d) (constantStrainL d) μ hμ
      hαV hβV hαE hβE hV' hE'
  have hpos := (compressedMeasure_positive_trace
    V.toForm E.toForm (correctorSubspace d) (constantStrainL d) μ hμ
      (stdOrthonormalBasis ℝ (Symmetric d))).1
  have hrep : IsSpectralRepresentation μ C.kernel (lowerRate αE βV) (upperRate βE αV) := by
    refine ⟨hpos, hsupport, hfinite, fun t ht => ?_⟩
    apply eq_of_inner_action_eq
    intro e g
    rw [C.kernel_eq]
    exact (compressedMeasure_memory V.toForm E.toForm (correctorSubspace d)
      (constantStrainL d) μ hμ hαV hβV hαE hβE hV' hE' t ht e g).symm
  have heq := spectral_representation_unique (div_pos hαE hβV) ν μ C.kernel hν hrep
  rwa [heq]

end KVApproximation.Spectral
