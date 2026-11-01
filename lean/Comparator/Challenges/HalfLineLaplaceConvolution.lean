module

public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.Analysis.Convolution

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Theorem 3.1, Laplace-domain recovery: exponentially integrable
Banach-valued factors give a genuinely integrable causal convolution.
The rate may be any real number for which the stated integrability holds. -/
theorem integrable_halfLineLaplace_posConvolution
    (L : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) (s : ℝ)
    (hf : IntegrableOn (fun t => Real.exp (-s * t) • f t) (Set.Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun t => Real.exp (-s * t) • g t) (Set.Ioi (0 : ℝ))) :
    IntegrableOn (fun t => Real.exp (-s * t) • posConvolution f g L volume t)
      (Set.Ioi (0 : ℝ)) := by
  sorry

/-- Theorem 3.1, Laplace-domain recovery: the Bochner transform of a
causal convolution equals the continuous bilinear pairing of the transforms. -/
theorem halfLineLaplace_posConvolution [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace G] (L : E →L[ℝ] F →L[ℝ] G)
    (f : ℝ → E) (g : ℝ → F) (s : ℝ)
    (hf : IntegrableOn (fun t => Real.exp (-s * t) • f t) (Set.Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun t => Real.exp (-s * t) • g t) (Set.Ioi (0 : ℝ))) :
    halfLineLaplace (posConvolution f g L volume) s =
      L (halfLineLaplace f s) (halfLineLaplace g s) := by
  sorry

end KVApproximation.Analysis
