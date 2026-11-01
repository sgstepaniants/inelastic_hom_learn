module

public import KVApproximation.KelvinVoigt.MaterialFields
public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.KelvinVoigt.StripFields
public import KVApproximation.OperatorTheory.Spectrum

/-!
# The relaxation operator's upper spectral edge
-/

@[expose] public section

noncomputable section

open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Homogenization

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`): the upper edge of the
full relaxation operator's spectrum, rather than the support of the compressed
memory measure. Positivity and compactness of the spectrum are separate results. -/
def upperSpectralEdge {d : ℕ} (V E : CoerciveField d) : ℝ :=
  OperatorTheory.upperSpectralEdge (H := (correctorSubspace d).toSubmodule)
    (cellRelaxation (d := d) V E)

/-- Proposition 4.7: the spectral-edge map on the admissible material class. -/
def materialSpectralEdge {d : ℕ} {αV βV γV αE βE γE : ℝ}
    (hαV : 0 < αV) (hαE : 0 < αE)
    (M : admissibleMaterials d αV βV γV αE βE γE) : ℝ :=
  upperSpectralEdge (materialViscosity hαV M) (materialElasticity hαE M)


end KVApproximation.KelvinVoigt
