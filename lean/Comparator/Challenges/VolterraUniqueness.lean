module

public import Mathlib.Analysis.Convolution

public section

open MeasureTheory Set

namespace KVApproximation.Analysis

variable {H F G : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Theorem 3.1, finite-time uniqueness: the integrated homogeneous
memory equation has only the zero continuous trajectory when the viscous
operator controls its norm. No equation is required beyond the finite horizon. -/
theorem eqOn_zero_of_integrated_memory_eq_zero {T : ℝ} (hT : 0 ≤ T)
    (q : ℝ → H) (hq : ContinuousOn q (Icc (0 : ℝ) T))
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (c : ℝ) (hc : 0 ≤ c)
    (hV : ∀ x : H, ‖x‖ ≤ c * ‖V x‖)
    (hbalance : ∀ t ∈ Icc (0 : ℝ) T,
      V (q t) + E (∫ r in (0 : ℝ)..t, q r) +
        posConvolution K q L volume t = 0) :
    EqOn q (fun _ => 0) (Icc (0 : ℝ) T) := by
  sorry

/-- Theorem 3.1, Green-balance uniqueness: continuous trajectories
with the same integrated memory balance coincide on the finite horizon.
The right-hand side may vary arbitrarily with time. -/
theorem eqOn_of_integrated_memory_eq {T : ℝ} (hT : 0 ≤ T)
    (u v : ℝ → H) (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hv : ContinuousOn v (Icc (0 : ℝ) T))
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (c : ℝ) (hc : 0 ≤ c)
    (hV : ∀ x : H, ‖x‖ ≤ c * ‖V x‖)
    (hbalance : ∀ t ∈ Icc (0 : ℝ) T,
      V (u t) + E (∫ r in (0 : ℝ)..t, u r) + posConvolution K u L volume t =
        V (v t) + E (∫ r in (0 : ℝ)..t, v r) + posConvolution K v L volume t) :
    EqOn u v (Icc (0 : ℝ) T) := by
  sorry

end KVApproximation.Analysis
