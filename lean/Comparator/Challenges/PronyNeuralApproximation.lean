module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import KVApproximation.KelvinVoigt.PronyProblem

/-!
# From Prony stress approximation to neural responses
-/

public section

open KVApproximation.Tensor KVApproximation.Approximation
open KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
variable {αV βV γV αE βE γE δ ε : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
variable (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE)
variable (hδ : 0 < δ) (hε : 0 < ε)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hd hVorder hγV hEorder hγE hδ hε S

/-- Theorem 4.4, completion of the proof in Appendix B.3
(`eq:ua_error_tolerances`): any strict uniform Prony error gap leaves
room for B.12–B.13 without adding scalar state coordinates. -/
theorem local_prony_neural_approximation (hspan : αE / βV < βE / αV)
    {m : ℕ} (hm : 0 < m)
    (herror : uniformPronyError C
      (localPronyModel S.measure (fun M => (C M).viscosity) (fun M => (C M).elasticity)
        (βE / βV) (αE / βV) (βE / αV) m) δ < ENNReal.ofReal ε) :
    let n := logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)) * m
    ∀ (Fclass : StressResponseClass d (n * strainDimension d))
      (Gclass : KineticResponseClass d (n * strainDimension d)),
      HasUniversalApproximation Fclass → HasLocallyLipschitzApproximation Gclass →
      ∃ F ∈ Fclass, ∃ G ∈ Gclass, UniformlyApproximates C F G δ ε := by
  sorry

/-- Theorems 4.4–4.5, singleton case: exact one-term Prony stress and
B.12–B.13 give neural approximation with one symmetric-tensor state. -/
theorem singleton_prony_neural_approximation (hspan : αE / βV = βE / αV) :
    ∀ (Fclass : StressResponseClass d (1 * strainDimension d))
      (Gclass : KineticResponseClass d (1 * strainDimension d)),
      HasUniversalApproximation Fclass → HasLocallyLipschitzApproximation Gclass →
      ∃ F ∈ Fclass, ∃ G ∈ Gclass, UniformlyApproximates C F G δ ε := by
  sorry

end KVApproximation.KelvinVoigt
