module

public import KVApproximation.Analysis.TimeSobolev
public import Mathlib.Analysis.Convolution

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {H F G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Theorem 3.1, recovery of the weak evolution equation: the
Banach-valued balance almost everywhere is equivalent to its integrated
identity at every closed-interval trace. The exceptional null set is chosen
before applying any continuous linear test functional. -/
theorem TimeH1.memory_equation_iff_integrated {T : ℝ} (hT : 0 < T)
    (u : TimeH1 H T) (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (g : ℝ → G)
    (hg : IntervalIntegrable g volume 0 T) :
    let q : ℝ → H := fun t => TimeH1.trace hT u (Set.projIcc 0 T hT.le t)
    (∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      V (TimeH1.velocity u t) + E (TimeH1.value u t) +
        posConvolution K (TimeH1.velocity u) L volume t = g t) ↔
    ∀ t : Set.Icc (0 : ℝ) T,
      V (q t - TimeH1.initial hT u) + E (∫ r in (0 : ℝ)..(t : ℝ), q r) +
        posConvolution K (fun r => q r - TimeH1.initial hT u) L volume t =
          ∫ r in (0 : ℝ)..(t : ℝ), g r := by
  sorry

end KVApproximation.Analysis
