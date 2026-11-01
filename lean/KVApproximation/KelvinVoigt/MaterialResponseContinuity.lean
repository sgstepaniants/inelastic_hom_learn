module

public import KVApproximation.KelvinVoigt.MaterialTopology
public import KVApproximation.KelvinVoigt.PronyContinuity
public import KVApproximation.Homogenization.CellConvergence
public import Mathlib.Topology.Sequences

/-!
# Continuous responses on the material class
-/

public section

open Filter
open scoped Topology
open KVApproximation.Tensor KVApproximation.Approximation KVApproximation.Homogenization

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE)

include hVorder hEorder

private theorem cell_tensors_tendsto
    {M : admissibleMaterials d αV βV γV αE βE γE}
    {Mseq : ℕ → admissibleMaterials d αV βV γV αE βE γE}
    (hM : Tendsto Mseq atTop (𝓝 M)) :
    Tendsto (fun n => (C (Mseq n)).viscosity) atTop (𝓝 (C M).viscosity) ∧
    Tendsto (fun n => (C (Mseq n)).elasticity) atTop (𝓝 (C M).elasticity) := by
  obtain ⟨hVconv, hEconv⟩ := material_fields_L1_tendsto hαV hαE hM
  exact effective_tensors_converge
    (materialViscosity hαV M) (materialElasticity hαE M)
    (fun n => materialViscosity hαV (Mseq n)) (fun n => materialElasticity hαE (Mseq n))
    hαV (hαV.trans_le hVorder) hαE (hαE.trans_le hEorder)
    (materialViscosity hαV M).bounds (materialElasticity hαE M).bounds
    (fun n => (materialViscosity hαV (Mseq n)).bounds)
    (fun n => (materialElasticity hαE (Mseq n)).bounds) hVconv hEconv
    (C M) (fun n => C (Mseq n))

/-- Corollary B.4: the effective viscosity is continuous in the material topology. -/
theorem continuous_cell_viscosity : Continuous (fun M => (C M).viscosity) := by
  apply continuous_iff_seqContinuous.mpr
  intro Mseq M hM
  exact (cell_tensors_tendsto hαV hVorder hαE hEorder C hM).1

/-- Corollary B.4: the effective elasticity is continuous in the material topology. -/
theorem continuous_cell_elasticity : Continuous (fun M => (C M).elasticity) := by
  apply continuous_iff_seqContinuous.mpr
  intro Mseq M hM
  exact (cell_tensors_tendsto hαV hVorder hαE hEorder C hM).2

variable (S : SpectralFamily C)

/-- Proposition B.10: every signed local coefficient is continuous on
the actual admissible material class. -/
theorem continuous_local_prony_coefficient (hspan : αE / βV < βE / αV)
    {m : ℕ} (hm : 0 < m)
    (j : Fin (logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)))) (i : Fin m) :
    Continuous (fun M => localPronyCoefficient (S.measure M)
      (βE / βV) (αE / βV) (βE / αV) m j i) := by
  apply continuous_iff_seqContinuous.mpr
  intro Mseq M hM
  obtain ⟨hVconv, hEconv⟩ := material_L1_tendsto hM
  exact local_prony_coefficient_converges hαV hVorder hαE hEorder C S M Mseq
    hVconv hEconv hspan hm j i

/-- Proposition B.10: the singleton coefficient is continuous on the
actual admissible material class. -/
theorem continuous_singleton_prony_coefficient (hspan : αE / βV = βE / αV) :
    Continuous (fun M => singletonPronyCoefficient (S.measure M)) := by
  apply continuous_iff_seqContinuous.mpr
  intro Mseq M hM
  obtain ⟨hVconv, hEconv⟩ := material_L1_tendsto hM
  exact singleton_prony_coefficient_converges hαV hVorder hαE hEorder C S M Mseq
    hVconv hEconv hspan

end KVApproximation.KelvinVoigt
