module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Dominated convergence in finite Lp spaces
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Dominated-convergence step used in Lemma B.1: an Lp majorant and a.e. convergence to zero
give convergence of the Lp norm, for every finite positive exponent. -/
theorem tendsto_eLpNorm_of_dominated_zero {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {p : ENNReal} (hp₀ : p ≠ 0) (hp_top : p ≠ ⊤)
    {F : ℕ → X → E} {bound : X → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hb : MemLp bound p μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p μ) atTop (𝓝 0) := by
  sorry

end KVApproximation.Analysis
