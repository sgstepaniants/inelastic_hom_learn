module

public import KVApproximation.OperatorTheory.CoerciveSolvers
public import Mathlib.Analysis.SpecialFunctions.Exponential

public section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, homogeneous microscopic evolution: the relative Riesz
semigroup has the actual Hilbert-valued time derivative. -/
theorem relativeSemigroup_hasDerivAt (V E : CoerciveForm H) (u : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (-s • relativeRiesz V E)) u)
      (-relativeRiesz V E ((NormedSpace.exp (-t • relativeRiesz V E)) u)) t := by
  sorry

/-- Theorem 3.1, uniform half-line estimate: homogeneous evolution
does not increase the viscous energy. -/
theorem relativeSemigroup_energy_le (V E : CoerciveForm H)
    (u : H) (t : ℝ) (ht : 0 ≤ t) :
    V.form ((NormedSpace.exp (-t • relativeRiesz V E)) u)
        ((NormedSpace.exp (-t • relativeRiesz V E)) u) ≤ V.form u u := by
  sorry

/-- Theorem 3.1, uniform half-line estimate: viscous norm equivalence
gives a semigroup bound independent of time. -/
theorem relativeSemigroup_norm_le (V E : CoerciveForm H) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (hV : V.HasBounds α β)
    (u : H) (t : ℝ) (ht : 0 ≤ t) :
    ‖(NormedSpace.exp (-t • relativeRiesz V E)) u‖ ≤ Real.sqrt (β / α) * ‖u‖ := by
  sorry

end KVApproximation.OperatorTheory
