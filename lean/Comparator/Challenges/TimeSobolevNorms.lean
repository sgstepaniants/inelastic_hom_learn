module

public import KVApproximation.Analysis.TimeSobolevCoordinates

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, time-space bounds: the value coordinate has the prescribed representative. -/
theorem TimeH1.valueL2_apply {T : ℝ} (u : TimeH1 H T) (t : ℝ) :
    TimeH1.valueL2 u t = TimeH1.value u t := by
  sorry

/-- Theorem 3.1, time-space bounds: the velocity coordinate has the prescribed
Hilbert-valued weak derivative almost everywhere. -/
theorem TimeH1.velocityL2_apply_ae {T : ℝ} (u : TimeH1 H T) :
    TimeH1.velocityL2 u =ᵐ[volume.restrict (Set.Ioo 0 T)] TimeH1.velocity u := by
  sorry

/-- Theorem 3.1, time-space bounds: the actual graph norm is the Euclidean
sum of the L² value and Hilbert-valued velocity norms. -/
theorem TimeH1.norm_sq_eq_value_velocity {T : ℝ} (u : TimeH1 H T) :
    ‖u‖ ^ 2 = ‖TimeH1.valueL2 u‖ ^ 2 + ‖TimeH1.velocityL2 u‖ ^ 2 := by
  sorry

/-- Theorem 3.1, time-space bounds: a bounded linear evolution controls
the full H¹ norm by the L² value and forcing norms. -/
theorem TimeH1.norm_le_of_ode {T : ℝ} (A : H →L[ℝ] H)
    (f : Lp H 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t) :
    ‖u‖ ≤ (1 + ‖A‖) * ‖TimeH1.valueL2 u‖ + ‖f‖ := by
  sorry

end KVApproximation.Analysis
