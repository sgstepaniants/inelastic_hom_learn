module

public import KVApproximation.KelvinVoigt.Material
public import KVApproximation.Tensor.MultiplicationIdentities

/-!
# Coercive fields associated with admissible materials
-/

@[expose] public section

noncomputable section

open KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Section 4.1: the viscosity field of an admissible material, passed
from the common L² topology to its essentially bounded representative. -/
def materialViscosity {d : ℕ} {αV βV γV αE βE γE : ℝ} (hαV : 0 < αV)
    (M : admissibleMaterials d αV βV γV αE βE γE) : CoerciveField d :=
  CoerciveField.ofMemLp M.val.1 M.property.1 αV βV hαV M.property.2.2.1

/-- Section 4.1: the elasticity field of an admissible material. -/
def materialElasticity {d : ℕ} {αV βV γV αE βE γE : ℝ} (hαE : 0 < αE)
    (M : admissibleMaterials d αV βV γV αE βE γE) : CoerciveField d :=
  CoerciveField.ofMemLp M.val.2 M.property.2.1 αE βE hαE M.property.2.2.2.1

end KVApproximation.KelvinVoigt
