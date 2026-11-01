module

public import KVApproximation.KelvinVoigt.PronyProblem
public import KVApproximation.Homogenization.WeightedSpectralContinuity
public import KVApproximation.Approximation.SpectralPartition

/-!
# Continuity of the signed Prony coefficients
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Spectral
open KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)
variable (M : admissibleMaterials d αV βV γV αE βE γE)
variable (Mseq : ℕ → admissibleMaterials d αV βV γV αE βE γE)
variable (hVconv : Tendsto
  (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (hEconv : Tendsto
  (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y) 1 (cellMeasure d)) atTop (𝓝 0))

include hVconv hEconv

/-- Proposition B.10: the essentially bounded representatives used by
the cell problems have the same L¹ convergence as the material fields. -/
private theorem material_field_convergence :
    Tendsto (fun n => eLpNorm (fun y =>
      (materialViscosity hαV (Mseq n)).field y - (materialViscosity hαV M).field y)
        1 (cellMeasure d)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun y =>
      (materialElasticity hαE (Mseq n)).field y - (materialElasticity hαE M).field y)
        1 (cellMeasure d)) atTop (𝓝 0) := by
  constructor
  · convert hVconv using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [(Mseq n).property.1.coeFn_toLp, M.property.1.coeFn_toLp] with y hy hz
    exact congrArg₂ (fun a b : Elasticity d => a - b) hy hz
  · convert hEconv using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [(Mseq n).property.2.1.coeFn_toLp, M.property.2.1.coeFn_toLp] with y hy hz
    exact congrArg₂ (fun a b : Elasticity d => a - b) hy hz

include hVorder hEorder

/-- Proposition B.10, coefficient continuity: L¹ convergence of admissible
materials gives convergence of every signed local coefficient. -/
theorem local_prony_coefficient_converges
    (_hspan : αE / βV < βE / αV) {m : ℕ} (_hm : 0 < m)
    (j : Fin (logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)))) (i : Fin m) :
    Tendsto (fun n => localPronyCoefficient (S.measure (Mseq n))
        (βE / βV) (αE / βV) (βE / αV) m j i)
      atTop (𝓝 (localPronyCoefficient (S.measure M) (βE / βV) (αE / βV) (βE / αV) m j i)) := by
  obtain ⟨hVconv', hEconv'⟩ := material_field_convergence hαV hαE M Mseq hVconv hEconv
  have h := weighted_spectral_measures_converge
    (materialViscosity hαV M) (materialElasticity hαE M)
    (fun n => materialViscosity hαV (Mseq n)) (fun n => materialElasticity hαE (Mseq n))
    (C M) (fun n => C (Mseq n)) hαV hVorder hαE hEorder
    (materialViscosity hαV M).bounds (materialElasticity hαE M).bounds
    (fun n => (materialViscosity hαV (Mseq n)).bounds)
    (fun n => (materialElasticity hαE (Mseq n)).bounds) hVconv' hEconv'
    (S.measure M) (fun n => S.measure (Mseq n)) (S.represents M) (fun n => S.represents (Mseq n))
    _ (continuousOn_localPronyWeight (div_pos hαE (hαV.trans_le hVorder)) m j i)
  exact h.2.2.const_smul _

/-- Proposition B.10, singleton coefficient continuity: the first spectral
moment is continuous under L¹ convergence of admissible materials. -/
theorem singleton_prony_coefficient_converges (_hspan : αE / βV = βE / αV) :
    Tendsto (fun n => singletonPronyCoefficient (S.measure (Mseq n)))
      atTop (𝓝 (singletonPronyCoefficient (S.measure M))) := by
  obtain ⟨hVconv', hEconv'⟩ := material_field_convergence hαV hαE M Mseq hVconv hEconv
  exact (spectral_measures_converge
    (materialViscosity hαV M) (materialElasticity hαE M)
    (fun n => materialViscosity hαV (Mseq n)) (fun n => materialElasticity hαE (Mseq n))
    (C M) (fun n => C (Mseq n)) hαV hVorder hαE hEorder
    (materialViscosity hαV M).bounds (materialElasticity hαE M).bounds
    (fun n => (materialViscosity hαV (Mseq n)).bounds)
    (fun n => (materialElasticity hαE (Mseq n)).bounds) hVconv' hEconv'
    (S.measure M) (fun n => S.measure (Mseq n)) (S.represents M) (fun n => S.represents (Mseq n))
    (fun r => r) continuousOn_id).2.2

end KVApproximation.KelvinVoigt
