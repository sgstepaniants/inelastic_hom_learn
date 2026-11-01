module

public import KVApproximation.Analysis.TimeSobolevCoordinates
public import Mathlib.Analysis.SpecialFunctions.Exponential

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.Dynamics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, forced evolution estimate: a semigroup bound and Cauchy–Schwarz
control the continuous trace on the entire closed interval. -/
theorem linear_timeH1_trace_norm_le (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {M : ℝ} (hM : 0 ≤ M)
    (hsemigroup : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : H,
      ‖(NormedSpace.exp (s • A)) x‖ ≤ M * ‖x‖)
    (f : Lp H 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t)
    (t : Set.Icc (0 : ℝ) T) :
    ‖TimeH1.trace hT u t‖ ≤ M * (‖TimeH1.initial hT u‖ + Real.sqrt T * ‖f‖) := by
  sorry

/-- Theorem 3.1, forced evolution estimate: the same semigroup bound
controls the actual full finite-time H¹ norm. -/
theorem linear_timeH1_norm_le (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {M : ℝ} (hM : 0 ≤ M)
    (hsemigroup : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : H,
      ‖(NormedSpace.exp (s • A)) x‖ ≤ M * ‖x‖)
    (f : Lp H 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t) :
    ‖u‖ ≤ (1 + ‖A‖) * Real.sqrt T *
      (M * (‖TimeH1.initial hT u‖ + Real.sqrt T * ‖f‖)) + ‖f‖ := by
  sorry

end KVApproximation.Dynamics
