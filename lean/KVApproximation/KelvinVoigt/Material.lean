module

public import KVApproximation.Tensor.Fields
public import KVApproximation.Analysis.PeriodicVariation

/-!
# The admissible material class
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Section 4.1 (`eq:admissible_microstructure`): viscosity and elasticity
fields in their common L² ambient space. -/
abbrev Material (d : ℕ) := CoefficientField d 2 × CoefficientField d 2

/-- Section 4.1 (`eq:admissible_microstructure`): the BV and uniform
ellipticity constraints defining the material class. No nonemptiness
condition is imposed. -/
def admissibleMaterials (d : ℕ) (αV βV γV αE βE γE : ℝ) : Set (Material d) :=
  {M | MemLp M.1 ⊤ (cellMeasure d) ∧ MemLp M.2 ⊤ (cellMeasure d) ∧
    HasFieldBounds αV βV M.1 ∧ HasFieldBounds αE βE M.2 ∧
    periodicBVNorm M.1 ≤ ENNReal.ofReal γV ∧
    periodicBVNorm M.2 ≤ ENNReal.ofReal γE}

end KVApproximation.KelvinVoigt
