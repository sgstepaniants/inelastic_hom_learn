module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Isometric coordinates for coefficient fields
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.12, material-coordinate step: a value-space linear isometry
induces an Lp linear isometry, acting pointwise almost everywhere. This
also covers infinite measures and `p = ∞`. -/
theorem lp_coordinates {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) (p : ENNReal) [Fact (1 ≤ p)] (T : E ≃ₗᵢ[ℝ] F) :
    ∃ U : Lp E p μ ≃ₗᵢ[ℝ] Lp F p μ,
      ∀ f : Lp E p μ, ∀ᵐ y ∂μ, U f y = T (f y) := by
  let A := T.toContinuousLinearEquiv.toContinuousLinearMap
  let B := T.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let J : Lp E p μ →ₗᵢ[ℝ] Lp F p μ :=
    { A.compLpₗ p μ with
      norm_map' := by
        intro f
        rw [Lp.norm_def, Lp.norm_def]
        congr 1
        apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
        filter_upwards [A.coeFn_compLp f] with y hy
        change ‖A.compLp f y‖ = ‖f y‖
        rw [hy]
        exact T.norm_map (f y) }
  have hJ : Function.Surjective J := by
    intro f
    refine ⟨B.compLp f, ?_⟩
    apply Lp.ext
    filter_upwards [A.coeFn_compLp (B.compLp f), B.coeFn_compLp f] with y hy hz
    change A.compLp (B.compLp f) y = f y
    rw [hy, hz]
    exact T.apply_symm_apply (f y)
  refine ⟨LinearIsometryEquiv.ofSurjective J hJ, ?_⟩
  intro f
  exact A.coeFn_compLp f

end KVApproximation.Analysis
