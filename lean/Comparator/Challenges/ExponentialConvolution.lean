module

public import KVApproximation.Dynamics.Trajectory
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.7, exponential-kernel estimate: the norm of the finite-time
convolution retains the factor `1 - exp(-Re(z) * t)`. -/
theorem norm_exponential_integral_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (f : ℝ → F) {M t : ℝ} {z : ℂ} (ht : 0 ≤ t) (hz : 0 < z.re)
    (hbound : ∀ᵐ s ∂volume.restrict (Set.Ioc 0 t), ‖f s‖ ≤ M) :
    ‖∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • f s‖ ≤
      M * (1 - Real.exp (-z.re * t)) / z.re := by
  sorry

end KVApproximation.Analysis

namespace KVApproximation.Dynamics

/-- Lemma B.7, integration by parts: the exponential convolution of the
velocity equals the endpoint terms minus the convolution of the value. -/
theorem BoundedTrajectory.exponential_integral_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →L[ℝ] F) (e : BoundedTrajectory E) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    (∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • J (e.velocity s)) =
      J (e.value t) - Complex.exp (-z * (t : ℂ)) • J (e.value 0) -
        z • ∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • J (e.value s) := by
  sorry

end KVApproximation.Dynamics
