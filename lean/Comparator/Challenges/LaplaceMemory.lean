module

public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.Analysis.Convolution

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), time-domain
recovery: the prepared transformed equation determines the integrated memory
balance at every nonnegative time. -/
theorem integrated_memory_eq_zero_of_halfLineLaplace
    {H F G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K)
    (hKi : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t => Real.exp (-s * t) • K t) (Set.Ioi (0 : ℝ)))
    (u : ℝ → H) (hu : ContinuousOn u (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ M) (u₀ : H)
    (hLap : ∀ s : ℝ, 0 < s →
      (V + s⁻¹ • E + L (halfLineLaplace K s))
        (s • halfLineLaplace u s - u₀) = -s⁻¹ • E u₀) :
    ∀ t : ℝ, 0 ≤ t →
      V (u t - u₀) + E (∫ r in (0 : ℝ)..t, u r) +
        posConvolution K (fun r => u r - u₀) L volume t = 0 := by
  sorry

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), viscously prepared
Green evolution: the transformed elliptic load gives a constant-load
integrated memory balance, including the viscous initial identity at zero. -/
theorem integrated_memory_eq_const_of_halfLineLaplace
    {H F G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K)
    (hKi : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t => Real.exp (-s * t) • K t) (Set.Ioi (0 : ℝ)))
    (u : ℝ → H) (hu : ContinuousOn u (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ M) (g : G)
    (hLap : ∀ s : ℝ, 0 < s →
      (V + s⁻¹ • E + L (halfLineLaplace K s)) (halfLineLaplace u s) = s⁻¹ • g) :
    ∀ t : ℝ, 0 ≤ t →
      V (u t) + E (∫ r in (0 : ℝ)..t, u r) + posConvolution K u L volume t = g := by
  sorry

end KVApproximation.Analysis
