module

public import KVApproximation.KelvinVoigt.PronyProblem

/-!
# Continuous responses on the material class
-/

public section

open KVApproximation.Tensor KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE)

include hVorder hEorder

/-- Corollary B.4: the effective viscosity is continuous in the material topology. -/
theorem continuous_cell_viscosity : Continuous (fun M => (C M).viscosity) := by
  sorry

/-- Corollary B.4: the effective elasticity is continuous in the material topology. -/
theorem continuous_cell_elasticity : Continuous (fun M => (C M).elasticity) := by
  sorry

variable (S : SpectralFamily C)

/-- Proposition B.10: every signed local coefficient is continuous on
the actual admissible material class. -/
theorem continuous_local_prony_coefficient (hspan : αE / βV < βE / αV)
    {m : ℕ} (hm : 0 < m)
    (j : Fin (logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)))) (i : Fin m) :
    Continuous (fun M => localPronyCoefficient (S.measure M)
      (βE / βV) (αE / βV) (βE / αV) m j i) := by
  sorry

/-- Proposition B.10: the singleton coefficient is continuous on the
actual admissible material class. -/
theorem continuous_singleton_prony_coefficient (hspan : αE / βV = βE / αV) :
    Continuous (fun M => singletonPronyCoefficient (S.measure M)) := by
  sorry

end KVApproximation.KelvinVoigt
