module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Exp

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Theorem 3.1, time-domain recovery: a continuous kernel and local
time integrability give a continuous memory term on the closed half-line. -/
theorem continuousOn_posConvolution_Ici
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    (hK : Continuous K)
    (hf : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable f volume 0 T) :
    ContinuousOn (posConvolution K f L volume) (Set.Ici (0 : ℝ)) := by
  sorry

/-- Theorem 3.1, damped integrated residual: an exponentially
integrable kernel acting on a bounded continuous trajectory gives a uniformly
bounded damped memory term, with the exact bilinear operator-norm factor. -/
theorem norm_exp_smul_posConvolution_le
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    (hK : Continuous K) (hf : ContinuousOn f (Set.Ici (0 : ℝ)))
    {M : ℝ} (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ M)
    {a : ℝ} (ha : 0 ≤ a)
    (hKi : IntegrableOn (fun r => Real.exp (-a * r) • K r) (Set.Ioi (0 : ℝ)))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Real.exp (-a * t) • posConvolution K f L volume t‖ ≤
      ‖L‖ * M * (∫ r in Set.Ioi (0 : ℝ), ‖Real.exp (-a * r) • K r‖) := by
  sorry

end KVApproximation.Analysis
