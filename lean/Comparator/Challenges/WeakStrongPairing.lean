module

public import Mathlib.Analysis.Normed.Operator.Bilinear

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
  sorry

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
  sorry

end KVApproximation.Analysis
