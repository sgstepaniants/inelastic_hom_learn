module

public import KVApproximation.Analysis.PeriodicRescaling
public import KVApproximation.Homogenization.StaticWeakProblem

/-!
# Periodic coefficients on a physical domain
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, microscopic coefficient field: the L∞ class of
`A(x/ε)` restricted to the physical domain. -/
def rescaledCoefficient {d : ℕ} (Ω : Opens (PhysicalSpace d))
    (A : CoefficientField d ⊤) (ε : ℝ) (hε : ε ≠ 0) :
    Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d))) :=
  ((memLp_top_rescalePeriodic hε (Lp.memLp A)).restrict (Ω : Set (PhysicalSpace d))).toLp
    (rescalePeriodic A ε)

end KVApproximation.Homogenization
