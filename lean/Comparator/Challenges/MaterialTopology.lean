module

public import KVApproximation.KelvinVoigt.MaterialFields

/-!
# Material topology and coefficient convergence
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE : ℝ}
variable {ι : Type*} {l : Filter ι}
variable {M : admissibleMaterials d αV βV γV αE βE γE}
variable {Mseq : ι → admissibleMaterials d αV βV γV αE βE γE}

/-- Lemma B.2 and Proposition B.10: convergence in the common L² material
topology implies L¹ convergence of both coefficient fields. -/
theorem material_L1_tendsto (hM : Tendsto Mseq l (𝓝 M)) :
    Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y)
      1 (cellMeasure d)) l (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y)
      1 (cellMeasure d)) l (𝓝 0) := by
  sorry

/-- Corollary B.4 and Proposition B.10: the bounded representatives used
by the cell problems preserve this convergence. -/
theorem material_fields_L1_tendsto (hαV : 0 < αV) (hαE : 0 < αE)
    (hM : Tendsto Mseq l (𝓝 M)) :
    Tendsto (fun n => eLpNorm (fun y =>
      (materialViscosity hαV (Mseq n)).field y - (materialViscosity hαV M).field y)
        1 (cellMeasure d)) l (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun y =>
      (materialElasticity hαE (Mseq n)).field y - (materialElasticity hαE M).field y)
        1 (cellMeasure d)) l (𝓝 0) := by
  sorry

end KVApproximation.KelvinVoigt
