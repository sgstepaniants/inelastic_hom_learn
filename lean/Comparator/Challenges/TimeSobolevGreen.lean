module

public import KVApproximation.Analysis.TimeSobolev
public import Mathlib.Analysis.Convolution

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), forced weak equation:
an H¹ realization of the Green convolution has zero initial value and
satisfies the memory equation almost everywhere on one common full-measure set. -/
theorem TimeH1.memory_equation_of_green_trace
    {F H Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {T : ℝ} (hT : 0 < T) (u : TimeH1 H T)
    (V E : H →L[ℝ] Y) (K : ℝ → H →L[ℝ] Y)
    (G : ℝ → F →L[ℝ] H) (B : F →L[ℝ] Y)
    (hK : Continuous K) (hG : Continuous G)
    (hbalance : ∀ (t : ℝ), 0 ≤ t → ∀ g : F,
      V (G t g) + E (∫ s in (0 : ℝ)..t, G s g) +
        (∫ s in (0 : ℝ)..t, K (t - s) (G s g)) = B g)
    (f : ℝ → F) (hf : IntervalIntegrable f volume 0 T)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T,
      TimeH1.trace hT u t = ∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) :
    TimeH1.initial hT u = 0 ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        V (TimeH1.velocity u t) + E (TimeH1.value u t) +
          posConvolution K (TimeH1.velocity u)
            (ContinuousLinearMap.id ℝ (H →L[ℝ] Y)) volume t = B (f t) := by
  sorry

end KVApproximation.Analysis
