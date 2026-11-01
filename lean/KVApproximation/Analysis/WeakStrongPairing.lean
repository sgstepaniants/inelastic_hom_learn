module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Bilinear pairings under weak and strong convergence

The varying strong factor contributes a norm-small error, uniformly in
the bounded weak factor. The remaining fixed pairing is a weak test.
-/

public section

open Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, oscillating-test errors: pairing an eventually bounded
factor with a factor tending strongly to zero gives a vanishing limit. -/
theorem tendsto_bilinear_zero_of_bounded
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} {l : Filter ι} {u : ι → E} {v : ι → F}
    (B : E →L[ℝ] F →L[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hv : Tendsto v l (𝓝 0)) :
    Tendsto (fun i => B (u i) (v i)) l (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun i => ‖B‖ * C * ‖v i‖)
  · filter_upwards [hbound] with i hi
    exact (B.le_opNorm₂ (u i) (v i)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hi (norm_nonneg B)) le_rfl
        (norm_nonneg _) (mul_nonneg (norm_nonneg B) hC))
  · simpa only [norm_zero, mul_zero] using hv.norm.const_mul (‖B‖ * C)

/-- Theorem 3.1, oscillating-test limits: a bounded weakly convergent
factor and a strongly convergent factor preserve every continuous bilinear pairing. -/
theorem tendsto_bilinear_of_weak_strong
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} {l : Filter ι} {u : ι → E} {v : ι → F} {u₀ : E} {v₀ : F}
    (B : E →L[ℝ] F →L[ℝ] ℝ)
    (hu : ∀ ℓ : E →L[ℝ] ℝ, Tendsto (fun i => ℓ (u i)) l (𝓝 (ℓ u₀)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => B (u i) (v i)) l (𝓝 (B u₀ v₀)) := by
  have herr : Tendsto (fun i => B (u i) (v i - v₀)) l (𝓝 0) := by
    apply tendsto_bilinear_zero_of_bounded B hC hbound
    simpa only [sub_self] using hv.sub (tendsto_const_nhds (x := v₀))
  have hfixed := hu (B.flip v₀)
  simpa only [map_sub, ContinuousLinearMap.flip_apply, sub_add_cancel, zero_add] using
    herr.add hfixed

end KVApproximation.Analysis
