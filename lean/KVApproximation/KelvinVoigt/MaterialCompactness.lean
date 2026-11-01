module

public import KVApproximation.KelvinVoigt.Material
public import KVApproximation.Tensor.FieldCompactness

/-!
# Compactness of admissible materials

The viscosity and elasticity coefficient classes are compact separately. Their
product carries the material L² topology used in the approximation theorem.
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Lemma B.2 (`lem:bv_compact`): compactness in the product L² topology
for the actual periodic BV material class. -/
theorem isCompact_admissibleMaterials {d : ℕ} (_hd : d ∈ ({1, 2, 3} : Set ℕ))
    {αV βV γV αE βE γE : ℝ}
    (hαV : 0 < αV) (hV : αV ≤ βV) (_hγV : 0 < γV)
    (hαE : 0 < αE) (hE : αE ≤ βE) (_hγE : 0 < γE) :
    IsCompact (admissibleMaterials d αV βV γV αE βE γE) := by
  have hVC := isCompact_coefficient_constraints (d := d) (C := ENNReal.ofReal γV)
    hαV.le (hαV.le.trans hV) ENNReal.ofReal_ne_top
  have hEC := isCompact_coefficient_constraints (d := d) (C := ENNReal.ofReal γE)
    hαE.le (hαE.le.trans hE) ENNReal.ofReal_ne_top
  convert hVC.prod hEC using 1
  ext M
  simp only [admissibleMaterials, Set.mem_ofPred_eq, Set.mem_prod]
  tauto

end KVApproximation.KelvinVoigt
