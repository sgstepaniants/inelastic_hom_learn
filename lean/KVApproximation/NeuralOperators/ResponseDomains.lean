module

public import KVApproximation.NeuralOperators.PronyResponses
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact input domains for the response maps
-/

public section

namespace KVApproximation.NeuralOperators

variable {E Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- Lemma B.12: the stress-budget and state-radius constraints form a
compact input domain. Negative budgets and radii simply allow an empty set. -/
theorem isCompact_stressInputSet {βE βV : ℝ} (hβE : 0 < βE) (hβV : 0 < βV)
    (δ radius : ℝ) : IsCompact (stressInputSet (E := E) (Q := Q) βE βV δ radius) := by
  have hx := WithLp.prod_continuous_ofLp 2 E (WithLp 2 (E × Q))
  have hy := (WithLp.prod_continuous_ofLp 2 E Q).comp hx.snd
  have hclosed : IsClosed (stressInputSet (E := E) (Q := Q) βE βV δ radius) :=
    (isClosed_le ((hx.fst.norm.const_mul βE).add (hy.fst.norm.const_mul βV))
      continuous_const).inter (isClosed_le hy.snd.norm continuous_const)
  let f : E × (E × Q) → StressInput E Q := fun y =>
    WithLp.toLp 2 (y.1, WithLp.toLp 2 y.2)
  have hf : Continuous f := (WithLp.prod_continuous_toLp 2 E (WithLp 2 (E × Q))).comp
    (continuous_fst.prodMk ((WithLp.prod_continuous_toLp 2 E Q).comp continuous_snd))
  have hc := ((isCompact_closedBall (0 : E) (δ / βE)).prod
    ((isCompact_closedBall (0 : E) (δ / βV)).prod (isCompact_closedBall (0 : Q) radius))).image hf
  apply hc.of_isClosed_subset hclosed
  intro x hmem
  have hfirst : ‖(WithLp.ofLp x).1‖ ≤ δ / βE := by
    apply (le_div_iff₀ hβE).mpr
    have hpos := mul_nonneg hβV.le (norm_nonneg (WithLp.ofLp (WithLp.ofLp x).2).1)
    have hbudget := hmem.1
    nlinarith
  have hsecond : ‖(WithLp.ofLp (WithLp.ofLp x).2).1‖ ≤ δ / βV := by
    apply (le_div_iff₀ hβV).mpr
    have hpos := mul_nonneg hβE.le (norm_nonneg (WithLp.ofLp x).1)
    have hbudget := hmem.1
    nlinarith
  refine ⟨((WithLp.ofLp x).1, WithLp.ofLp (WithLp.ofLp x).2), ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hfirst
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hsecond
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hmem.2
  · simp only [f, WithLp.toLp_ofLp, Prod.eta]

/-- Lemma B.12: the projected velocity-state domain is compact. -/
theorem isCompact_kineticInputSet {βV : ℝ} (hβV : 0 < βV)
    (δ radius : ℝ) : IsCompact (kineticInputSet (E := E) (Q := Q) βV δ radius) := by
  have hx := WithLp.prod_continuous_ofLp 2 E Q
  have hclosed : IsClosed (kineticInputSet (E := E) (Q := Q) βV δ radius) :=
    (isClosed_le (hx.fst.norm.const_mul βV) continuous_const).inter
      (isClosed_le hx.snd.norm continuous_const)
  have hc := ((isCompact_closedBall (0 : E) (δ / βV)).prod
    (isCompact_closedBall (0 : Q) radius)).image (WithLp.prod_continuous_toLp 2 E Q)
  apply hc.of_isClosed_subset hclosed
  intro x hmem
  refine ⟨WithLp.ofLp x, ⟨?_, ?_⟩, WithLp.toLp_ofLp 2 x⟩
  · simp only [Metric.mem_closedBall, dist_zero_right]
    exact (le_div_iff₀ hβV).mpr (by simpa only [mul_comm] using hmem.1)
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hmem.2

end KVApproximation.NeuralOperators
