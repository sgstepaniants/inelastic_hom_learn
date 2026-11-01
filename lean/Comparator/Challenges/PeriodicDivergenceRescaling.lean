module

public import KVApproximation.Analysis.PeriodicDivergence
public import KVApproximation.Analysis.PeriodicRescaling
public import KVApproximation.Analysis.VectorSobolev
public import TauCeti.Analysis.Sobolev.W1p.Zero

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, static flux tests: periodic zero divergence is
preserved by physical rescaling and holds against every scalar Dirichlet test. -/
theorem HasPeriodicZeroDivergence.integral_rescale_gradient_eq_zero {d : ℕ}
    {q : Lp (PhysicalSpace d) 2 (cellMeasure d)} (h : HasPeriodicZeroDivergence q)
    {Ω : Opens (PhysicalSpace d)} (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (v : TauCeti.W1p volume Ω 2) (hv : v ∈ TauCeti.w1p0Submodule volume Ω 2) :
    (∫ x in (Ω : Set (PhysicalSpace d)),
      ⟪rescalePeriodic q ε x, TauCeti.W1p.gradient v x⟫_ℝ) = 0 := by
  sorry

end KVApproximation.Analysis
