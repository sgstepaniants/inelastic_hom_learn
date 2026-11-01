module

public import KVApproximation.Homogenization.SpectralContinuity
public import KVApproximation.Spectral.WeightedMeasureIntegration

/-!
# Weak continuity after resolvent weighting
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Homogenization

namespace KVApproximation.Spectral

variable {d : ℕ} {αV βV αE βE : ℝ}
variable (V E : CoerciveField d) (Vseq Eseq : ℕ → CoerciveField d)
variable (C : CellConstitutiveModel V E)
variable (Cseq : ∀ n, CellConstitutiveModel (Vseq n) (Eseq n))
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field)
variable (hVseq : ∀ n, HasFieldBounds αV βV (Vseq n).field)
variable (hEseq : ∀ n, HasFieldBounds αE βE (Eseq n).field)
variable (hVconv : Tendsto
  (fun n => eLpNorm (fun y => (Vseq n).field y - V.field y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (hEconv : Tendsto
  (fun n => eLpNorm (fun y => (Eseq n).field y - E.field y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (ν : TensorMeasure d) (νseq : ℕ → TensorMeasure d)
variable (hν : IsSpectralRepresentation ν C.kernel (lowerRate αE βV) (upperRate βE αV))
variable (hνseq : ∀ n, IsSpectralRepresentation (νseq n) (Cseq n).kernel
  (lowerRate αE βV) (upperRate βE αV))

include C Cseq hαV hVorder hαE hEorder hV hE hVseq hEseq hVconv hEconv hν hνseq

/-- Lemma B.6 (`lem:weighted_spectral_measure`), continuity assertion:
the same weak convergence holds after multiplication by the resolvent weight. -/
theorem weighted_spectral_measures_converge (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (lowerRate αE βV) (upperRate βE αV))) :
    Integrable f (weightedMeasure (βE / βV) ν).variation ∧
      (∀ n, Integrable f (weightedMeasure (βE / βV) (νseq n)).variation) ∧
      Tendsto (fun n => tensorIntegral (weightedMeasure (βE / βV) (νseq n)) f)
        atTop (𝓝 (tensorIntegral (weightedMeasure (βE / βV) ν) f)) := by
  have hβV := hαV.trans_le hVorder
  have hβE := hαE.trans_le hEorder
  have hlower : 0 < lowerRate αE βV := div_pos hαE hβV
  have hc : 0 < βE / βV := div_pos hβE hβV
  have hwcont : ContinuousOn (resolventWeight (βE / βV))
      (Set.Icc (lowerRate αE βV) (upperRate βE αV)) :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun r hr => (add_pos hc (hlower.trans_le hr.1)).ne')
  have hi := weightedMeasure_integral hlower hc ν hν.1 hν.2.1 hν.2.2.1 f hf
  have his (n) := weightedMeasure_integral hlower hc (νseq n)
    (hνseq n).1 (hνseq n).2.1 (hνseq n).2.2.1 f hf
  refine ⟨hi.1, fun n => (his n).1, ?_⟩
  have h := (spectral_measures_converge V E Vseq Eseq C Cseq
    hαV hVorder hαE hEorder hV hE hVseq hEseq hVconv hEconv ν νseq hν hνseq
    (fun r => f r * resolventWeight (βE / βV) r) (hf.mul hwcont)).2.2
  simpa only [hi.2, (his _).2] using h

end KVApproximation.Spectral
