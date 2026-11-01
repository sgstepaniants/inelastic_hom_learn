module

public import KVApproximation.Approximation.AlternativeProny
public import KVApproximation.KelvinVoigt.PronyProblem

/-!
# Rates and continuity of the alternative Prony constructions
-/

public section

namespace KVApproximation.Approximation

/-- Remark 4.6: every global reference node gives a rate in the common
spectral interval, including a singleton interval. -/
theorem globalLogRate_mem {lower upper x : ℝ} (hlower : 0 < lower)
    (horder : lower ≤ upper) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    globalLogRate lower upper x ∈ Set.Icc lower upper := by
  sorry

end KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

open KVApproximation.Tensor KVApproximation.Approximation

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
  sorry

/-- Remark 4.6, applying the continuity argument of Proposition B.10:
the signed coefficients of one global interpolant are continuous on
the actual admissible material class. -/
theorem continuous_globalPronyCoefficient (n : ℕ) (i : Fin n) :
    Continuous (fun M => globalPronyCoefficient (S.measure M)
      (βE / βV) (αE / βV) (βE / αV) n i) := by
  sorry

end KVApproximation.KelvinVoigt
