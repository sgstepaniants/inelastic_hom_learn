module

public import KVApproximation.Analysis.TimeSobolev
public import Mathlib.Analysis.Convolution

public section

open MeasureTheory Set

namespace KVApproximation.Analysis

variable {H F G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Theorem 3.1, finite-time weak uniqueness: two Sobolev trajectories
with the same initial value and forcing coincide under the viscous norm bound.
Both competitors are defined only on the stated finite horizon. -/
theorem TimeH1.eq_of_memory_equation {T : ℝ} (hT : 0 < T)
    (u v : TimeH1 H T) (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (g : ℝ → G)
    (hg : IntervalIntegrable g volume 0 T) (c : ℝ) (hc : 0 ≤ c)
    (hV : ∀ x : H, ‖x‖ ≤ c * ‖V x‖)
    (hinit : TimeH1.initial hT u = TimeH1.initial hT v)
    (hu : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      V (TimeH1.velocity u t) + E (TimeH1.value u t) +
        posConvolution K (TimeH1.velocity u) L volume t = g t)
    (hv : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      V (TimeH1.velocity v t) + E (TimeH1.value v t) +
        posConvolution K (TimeH1.velocity v) L volume t = g t) : u = v := by
  sorry

end KVApproximation.Analysis
