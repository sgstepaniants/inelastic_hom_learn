module

public import KVApproximation.KelvinVoigt.Material

/-!
# Compactness of the material class
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis

namespace KVApproximation.KelvinVoigt

/-- Lemma B.2 (`lem:bv_compact`): compactness in the product L² topology
for the actual periodic BV material class. -/
theorem isCompact_admissibleMaterials {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
    {αV βV γV αE βE γE : ℝ}
    (hαV : 0 < αV) (hV : αV ≤ βV) (hγV : 0 < γV)
    (hαE : 0 < αE) (hE : αE ≤ βE) (hγE : 0 < γE) :
    IsCompact (admissibleMaterials d αV βV γV αE βE γE) := by
  sorry

/-- Lemma B.2 and Corollary B.4 (`lem:bv_compact`, `cor:continuity_tensors`):
an L¹ limit of admissible materials remains admissible, including its BV bounds.
The ambient L² assumption follows automatically from the common L-infinity bound. -/
theorem admissibleMaterials_mem_of_tendsto_L1 {d : ℕ}
    (hd : d ∈ ({1, 2, 3} : Set ℕ)) {αV βV γV αE βE γE : ℝ}
    (hαV : 0 < αV) (hV : αV ≤ βV) (hγV : 0 < γV)
    (hαE : 0 < αE) (hE : αE ≤ βE) (hγE : 0 < γE)
    {M : Material d} {Mseq : ℕ → Material d}
    (hseq : ∀ n, Mseq n ∈ admissibleMaterials d αV βV γV αE βE γE)
    (hVconv : Tendsto
      (fun n => eLpNorm (fun y => (Mseq n).1 y - M.1 y) 1 (cellMeasure d)) atTop (𝓝 0))
    (hEconv : Tendsto
      (fun n => eLpNorm (fun y => (Mseq n).2 y - M.2 y) 1 (cellMeasure d)) atTop (𝓝 0)) :
    M ∈ admissibleMaterials d αV βV γV αE βE γE := by
  sorry

end KVApproximation.KelvinVoigt
