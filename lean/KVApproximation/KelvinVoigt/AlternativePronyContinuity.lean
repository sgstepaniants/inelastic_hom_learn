module

public import KVApproximation.Approximation.AlternativeProny
public import KVApproximation.Approximation.SpectralPartition
public import KVApproximation.KelvinVoigt.PronyProblem
public import KVApproximation.KelvinVoigt.MaterialTopology
public import KVApproximation.Homogenization.WeightedSpectralContinuity
public import Mathlib.Topology.Sequences

/-!
# Continuity of alternative Prony coefficients
-/

public section

open Filter
open scoped Topology
open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hVorder hEorder

/-- Remark 4.6, applying the continuity argument of Proposition B.10:
the signed coefficients of the unweighted construction are continuous
on the actual admissible material class. -/
theorem continuous_unweightedLocalCoefficient (m : ℕ)
    (j : Fin (logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)))) (i : Fin m) :
    Continuous (fun M => unweightedLocalCoefficient (S.measure M)
      (αE / βV) (βE / αV) m j i) := by
  apply continuous_iff_seqContinuous.mpr
  intro Mseq M hM
  obtain ⟨hVconv, hEconv⟩ := material_fields_L1_tendsto hαV hαE hM
  have h := spectral_measures_converge
    (materialViscosity hαV M) (materialElasticity hαE M)
    (fun n => materialViscosity hαV (Mseq n)) (fun n => materialElasticity hαE (Mseq n))
    (C M) (fun n => C (Mseq n)) hαV hVorder hαE hEorder
    (materialViscosity hαV M).bounds (materialElasticity hαE M).bounds
    (fun n => (materialViscosity hαV (Mseq n)).bounds)
    (fun n => (materialElasticity hαE (Mseq n)).bounds) hVconv hEconv
    (S.measure M) (fun n => S.measure (Mseq n)) (S.represents M) (fun n => S.represents (Mseq n))
    _ (continuousOn_localPronyWeight (div_pos hαE (hαV.trans_le hVorder)) m j i)
  exact h.2.2.const_smul _

/-- Remark 4.6, applying the continuity argument of Proposition B.10:
the signed coefficients of one global interpolant are continuous on
the actual admissible material class. -/
theorem continuous_globalPronyCoefficient (n : ℕ) (i : Fin n) :
    Continuous (fun M => globalPronyCoefficient (S.measure M)
      (βE / βV) (αE / βV) (βE / αV) n i) := by
  have hlower : 0 < αE / βV := div_pos hαE (hαV.trans_le hVorder)
  have hcoord : ContinuousOn (globalLogCoordinate (αE / βV) (βE / αV))
      (Set.Icc (αE / βV) (βE / αV)) := by
    intro r hr
    have hlog : ContinuousAt (fun r : ℝ => Real.log (r / (αE / βV))) r :=
      (continuousAt_id.div_const _).log (div_pos (hlower.trans_le hr.1) hlower).ne'
    exact (((continuousAt_const.mul hlog).div_const _).sub continuousAt_const).continuousWithinAt
  have htest := (chebyshevLagrange n i).continuous.continuousOn.comp hcoord (Set.mapsTo_univ _ _)
  apply continuous_iff_seqContinuous.mpr
  intro Mseq M hM
  obtain ⟨hVconv, hEconv⟩ := material_fields_L1_tendsto hαV hαE hM
  have h := weighted_spectral_measures_converge
    (materialViscosity hαV M) (materialElasticity hαE M)
    (fun k => materialViscosity hαV (Mseq k)) (fun k => materialElasticity hαE (Mseq k))
    (C M) (fun k => C (Mseq k)) hαV hVorder hαE hEorder
    (materialViscosity hαV M).bounds (materialElasticity hαE M).bounds
    (fun k => (materialViscosity hαV (Mseq k)).bounds)
    (fun k => (materialElasticity hαE (Mseq k)).bounds) hVconv hEconv
    (S.measure M) (fun k => S.measure (Mseq k)) (S.represents M) (fun k => S.represents (Mseq k))
    _ htest
  exact h.2.2.const_smul _

end KVApproximation.KelvinVoigt
