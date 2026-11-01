module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Uniqueness for locally Lipschitz measurable-input equations
-/

public section

open MeasureTheory Set

namespace KVApproximation.Dynamics

/-- Proposition B.13, uniqueness for the original kinetic response:
local Lipschitz continuity and a bounded measurable input suffice for
uniqueness of continuous integral solutions on a finite interval. -/
theorem locally_lipschitz_driven_unique_Icc
    {V Q : Type*} [NormedAddCommGroup V] [ProperSpace V]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {G : V × Q → Q} (hG : LocallyLipschitz G)
    {v : ℝ → V} {a b R : ℝ}
    (hv : AEStronglyMeasurable v (volume.restrict (Icc a b)))
    (hR : ∀ᵐ s ∂volume.restrict (Icc a b), ‖v s‖ ≤ R)
    {x₀ : Q} {x₁ x₂ : ℝ → Q}
    (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = x₀ + ∫ s in a..t, G (v s, x₁ s))
    (h₂ : ∀ t ∈ Icc a b, x₂ t = x₀ + ∫ s in a..t, G (v s, x₂ s)) :
    EqOn x₁ x₂ (Icc a b) := by
  sorry

end KVApproximation.Dynamics
