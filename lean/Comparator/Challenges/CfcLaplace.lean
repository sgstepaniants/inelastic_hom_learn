module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import KVApproximation.Analysis.HalfLineLaplaceProperties

public section

open MeasureTheory KVApproximation.Analysis

namespace KVApproximation.OperatorTheory

/-- Theorem 3.1, transform of the relaxation kernel: the positive
self-adjoint spectral function r exp(-tr) is Bochner integrable in operator
norm after multiplication by any positive-rate exponential. -/
theorem integrable_cfc_memory_laplace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (R : H →L[ℝ] H)
    (hR : IsSelfAdjoint R) (hpos : ∀ r ∈ spectrum ℝ R, 0 ≤ r)
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) •
      cfc (fun r : ℝ => r * Real.exp (-r * t)) R) (Set.Ioi (0 : ℝ)) := by
  sorry

/-- Theorem 3.1, transform of the relaxation kernel: integrating the
continuous functional calculus gives the exact resolvent multiplier r/(s+r).
The underlying Hilbert space need not be finite-dimensional or separable. -/
theorem halfLineLaplace_cfc_memory {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (R : H →L[ℝ] H)
    (hR : IsSelfAdjoint R) (hpos : ∀ r ∈ spectrum ℝ R, 0 ≤ r)
    {s : ℝ} (hs : 0 < s) :
    halfLineLaplace (fun t : ℝ => cfc (fun r : ℝ => r * Real.exp (-r * t)) R) s =
      cfc (fun r : ℝ => r / (s + r)) R := by
  sorry

end KVApproximation.OperatorTheory
