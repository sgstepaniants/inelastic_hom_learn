module

public import Mathlib.Analysis.Convolution

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel limit:
pointwise weak convergence of uniformly bounded continuous operator kernels
passes through causal convolution with an L¹ forcing on a finite horizon.
The target may be any real Banach space; no separability is assumed. -/
theorem tendsto_intervalIntegral_of_weak_operator_tendsto
    {I F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {l : Filter I} [l.IsCountablyGenerated]
    (A : I → ℝ → F →L[ℝ] H) (G : ℝ → F →L[ℝ] H)
    (hA : ∀ i, Continuous (A i)) (hG : Continuous G)
    {C : ℝ} (hbound : ∀ (i : I) (t : ℝ), 0 ≤ t → ‖A i t‖ ≤ C)
    (hweak : ∀ (t : ℝ), 0 ≤ t → ∀ (g : F) (ℓ : H →L[ℝ] ℝ),
      Tendsto (fun i => ℓ (A i t g)) l (𝓝 (ℓ (G t g))))
    (f : ℝ → F) {T : ℝ} (hf : IntervalIntegrable f volume 0 T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (∫ r in (0 : ℝ)..t, A i (t - r) (f r))) l
        (𝓝 (ℓ (∫ r in (0 : ℝ)..t, G (t - r) (f r)))) := by
  sorry

end KVApproximation.Analysis
