module

public import KVApproximation.Analysis.PeriodicFourierCoefficients
public import KVApproximation.Analysis.PeriodicWeakGradient
public import KVApproximation.Analysis.PeriodicSobolevIdentities

/-!
# Identification of periodic Sobolev jets
-/

public section

namespace KVApproximation.Analysis

/-- Section 3.1: weak-gradient uniqueness identifies H¹ jets with their values. -/
theorem PeriodicH1.valueL_injective (d : ℕ) :
    Function.Injective (PeriodicH1.valueL d) := by
  intro u v hv
  have hg : PeriodicH1.gradientL d u = PeriodicH1.gradientL d v := by
    have hu := PeriodicH1.hasWeakGradient u
    rw [hv] at hu
    exact hu.gradient_unique (PeriodicH1.hasWeakGradient v)
  have hnorm := PeriodicH1.norm_sq (u - v)
  simp only [map_sub, hv, hg, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_add] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))

end KVApproximation.Analysis
