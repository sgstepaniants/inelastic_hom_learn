module

public import KVApproximation.KelvinVoigt.Constitutive
public import KVApproximation.Approximation.PronyModels
public import KVApproximation.Approximation.Constants

/-!
# Spectral families and uniform Prony error
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Dynamics

namespace KVApproximation.KelvinVoigt

/-- Proposition 3.3, for the material class of Theorem 4.4: a finite positive
measure representing each cell kernel on the common spectral interval. -/
structure SpectralFamily {d : ℕ} {αV βV γV αE βE γE : ℝ}
    {hαV : 0 < αV} {hαE : 0 < αE}
    (C : CellFamily d αV βV γV αE βE γE hαV hαE) where
  measure : admissibleMaterials d αV βV γV αE βE γE → TensorMeasure d
  represents : ∀ M, IsSpectralRepresentation (measure M) (C M).kernel (αE / βV) (βE / αV)

/-- Proposition B.10 (`eq:prony_homogenized_error_uniform`): the uniform
essential-supremum stress error. Supremums in `ENNReal` assign zero to an empty
material class without a nonemptiness hypothesis. -/
def uniformPronyError {d n : ℕ} {αV βV γV αE βE γE : ℝ}
    {hαV : 0 < αV} {hαE : 0 < αE}
    (C : CellFamily d αV βV γV αE βE γE hαV hαE)
    (P : PronyModel (admissibleMaterials d αV βV γV αE βE γE) (Symmetric d) n)
    (δ : ℝ) : ENNReal :=
  ⨆ M, ⨆ (e : BoundedTrajectory (Symmetric d)), ⨆ (_ : e.Admissible βE βV δ),
    eLpNorm (fun t => constitutiveStress (C M) e t - P.stress M e t) ⊤ timeMeasure

end KVApproximation.KelvinVoigt
