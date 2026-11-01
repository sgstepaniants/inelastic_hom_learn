module

public import KVApproximation.Homogenization.RescaledFields

public section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, combined elliptic coefficient: periodic rescaling
commutes with coefficient combinations as an equality of L∞ classes. -/
theorem rescaledCoefficient_add_smul {d : ℕ} (Ω : Opens (PhysicalSpace d))
    (A B : CoefficientField d ⊤) (c ε : ℝ) (hε : ε ≠ 0) :
    rescaledCoefficient Ω (A + c • B) ε hε =
      rescaledCoefficient Ω A ε hε + c • rescaledCoefficient Ω B ε hε := by
  sorry

/-- Theorem 3.1, transformed weak equation: the actual rescaled spatial
form splits into its viscous and elastic terms on any open domain. -/
theorem spatialForm_rescalePeriodic_add_smul {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A B : CoefficientField d ⊤) (c ε : ℝ) (hε : ε ≠ 0)
    (u v : ZeroBoundaryH1 Ω) :
    spatialForm (rescalePeriodic (A + c • B) ε) u v =
      spatialForm (rescalePeriodic A ε) u v +
        c * spatialForm (rescalePeriodic B ε) u v := by
  sorry

end KVApproximation.Homogenization
