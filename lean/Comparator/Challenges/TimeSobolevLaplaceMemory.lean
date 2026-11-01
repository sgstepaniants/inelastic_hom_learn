module

public import KVApproximation.Analysis.TimeSobolev
public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.Analysis.Convolution

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), weak-equation
recovery: a bounded continuous half-line extension of the Sobolev trace and
its prepared transformed equation imply the memory balance almost everywhere,
on one common full-measure set of times. -/
theorem TimeH1.memory_equation_of_halfLineLaplace
    {H F G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {T : ℝ} (hT : 0 < T) (u : TimeH1 H T)
    (v : ℝ → H) (hv : ContinuousOn v (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace hT u t = v t)
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K)
    (hKi : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t => Real.exp (-s * t) • K t) (Set.Ioi (0 : ℝ)))
    (hLap : ∀ s : ℝ, 0 < s →
      (V + s⁻¹ • E + L (halfLineLaplace K s))
        (s • halfLineLaplace v s - TimeH1.initial hT u) =
          -s⁻¹ • E (TimeH1.initial hT u)) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      V (TimeH1.velocity u t) + E (TimeH1.value u t) +
        posConvolution K (TimeH1.velocity u) L volume t = 0 := by
  sorry

end KVApproximation.Analysis
