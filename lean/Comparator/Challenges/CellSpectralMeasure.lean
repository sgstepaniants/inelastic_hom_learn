module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Spectral.Compression
public import KVApproximation.Spectral.Bounds

public section

open KVApproximation.Tensor KVApproximation.Homogenization

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
  sorry

end KVApproximation.Spectral
