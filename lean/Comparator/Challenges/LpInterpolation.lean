module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The L¹–L∞ interpolation step
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Lemma B.2 (`lem:bv_compact`), Hölder step: an essential pointwise bound
controls the squared L² norm by the L¹ norm, with constant one. -/
theorem eLpNorm_two_sq_le_of_ae_bound {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} {f : X → F} {κ : ℝ}
    (hf : AEStronglyMeasurable f μ) (hκ : 0 ≤ κ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ κ) :
    (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal κ * eLpNorm f 1 μ := by
  sorry

/-- Lemma B.2 (`lem:bv_compact`): L¹ convergence and a common essential bound
give L² convergence. The argument requires no finite-measure hypothesis. -/
theorem tendsto_eLpNorm_two_of_one_of_ae_bound {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} {f : ℕ → X → F} {κ : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hκ : 0 ≤ κ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ κ)
    (hconv : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  sorry

end KVApproximation.Analysis
