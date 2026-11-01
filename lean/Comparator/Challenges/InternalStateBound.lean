module

public import KVApproximation.KelvinVoigt.PronyProblem
public import KVApproximation.Tensor.MandelBlocks

/-!
# Uniform bounds for the material-dependent internal variables
-/

public section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Approximation KVApproximation.Dynamics

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
variable {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
variable (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE) (hδ : 0 < δ)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hd hVorder hγV hEorder hγE hδ

/-- Lemma B.11 (`lem:ua_step3_targets`): all local Prony internal variables,
in the prescribed scalar Mandel coordinates, have one uniform L∞ bound
over the full half-line and the actual material and strain classes. -/
theorem local_prony_state_uniform_bound (hspan : αE / βV < βE / αV)
    {m : ℕ} (hm : 0 < m) :
    let P := localPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) m
    ∃ δIV : ℝ, 0 < δIV ∧
      (⨆ M, ⨆ (e : BoundedTrajectory (Symmetric d)), ⨆ (_ : e.Admissible βE βV δ),
        eLpNorm (fun t => blockStrainMandel (P.state M e t)) ⊤ timeMeasure) ≤
          ENNReal.ofReal δIV := by
  sorry

/-- Lemma B.11, singleton spectral interval: the exact one-term model
has the same full-half-line uniform scalar-state bound. -/
theorem singleton_prony_state_uniform_bound (hspan : αE / βV = βE / αV) :
    let P := singletonPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (αE / βV)
    ∃ δIV : ℝ, 0 < δIV ∧
      (⨆ M, ⨆ (e : BoundedTrajectory (Symmetric d)), ⨆ (_ : e.Admissible βE βV δ),
        eLpNorm (fun t => blockStrainMandel (P.state M e t)) ⊤ timeMeasure) ≤
          ENNReal.ofReal δIV := by
  sorry

end KVApproximation.KelvinVoigt
