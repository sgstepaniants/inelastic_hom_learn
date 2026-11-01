module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Spectral.Bounds
public import KVApproximation.Spectral.TensorMeasure

/-!
# Weak continuity of spectral measures
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Homogenization

namespace KVApproximation.Spectral

/-- Proposition 3.3, uniqueness of its measure on a positive compact interval.
This identifies any finite positive representation with the measure obtained
by compressing the relaxation operator's spectral resolution. -/
theorem spectral_representation_unique {d : ℕ} {lower upper : ℝ}
    (hlower : 0 < lower) (ν₁ ν₂ : TensorMeasure d) (K : ℝ → Elasticity d)
    (hν₁ : IsSpectralRepresentation ν₁ K lower upper)
    (hν₂ : IsSpectralRepresentation ν₂ K lower upper) : ν₁ = ν₂ := by
  sorry

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

/-- Lemma B.5 (`lem:weak_convergence`): integration against every continuous
test on the common interval converges in the finite-dimensional tensor space.
The proof uses polynomial approximation and strong convergence of powers of R.
Integrability makes the totalized vector integrals agree with those in the paper. -/
theorem spectral_measures_converge (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (lowerRate αE βV) (upperRate βE αV))) :
    Integrable f ν.variation ∧ (∀ n, Integrable f (νseq n).variation) ∧
      Tendsto (fun n => tensorIntegral (νseq n) f) atTop (𝓝 (tensorIntegral ν f)) := by
  sorry

/-- Lemma B.6 (`lem:weighted_spectral_measure`), continuity assertion:
the same weak convergence holds after multiplication by the resolvent weight. -/
theorem weighted_spectral_measures_converge (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (lowerRate αE βV) (upperRate βE αV))) :
    Integrable f (weightedMeasure (βE / βV) ν).variation ∧
      (∀ n, Integrable f (weightedMeasure (βE / βV) (νseq n)).variation) ∧
      Tendsto (fun n => tensorIntegral (weightedMeasure (βE / βV) (νseq n)) f)
        atTop (𝓝 (tensorIntegral (weightedMeasure (βE / βV) ν) f)) := by
  sorry

end KVApproximation.Spectral
