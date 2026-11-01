module

public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.MeasureTheory.Integral.IntegrableOn

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, Laplace-domain argument: bounded continuous trajectories
have genuine Bochner-integrable transforms at every positive real rate. -/
theorem integrable_halfLineLaplace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℝ → F) (hu : ContinuousOn u (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖u t‖ ≤ M) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t => Real.exp (-s * t) • u t) (Set.Ioi (0 : ℝ)) := by
  sorry

/-- Theorem 3.1, Laplace convergence: a common half-line bound and
pointwise weak convergence imply weak convergence of the Bochner transforms.
The rate and functional are chosen after the convergent sequence. -/
theorem halfLineLaplace_weak_tendsto {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (u : ℕ → ℝ → F) (uLim : ℝ → F)
    (hu : ∀ n, ContinuousOn (u n) (Set.Ici (0 : ℝ)))
    (hLim : ContinuousOn uLim (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ n t, 0 ≤ t → ‖u n t‖ ≤ M)
    (hLimBound : ∀ t, 0 ≤ t → ‖uLim t‖ ≤ M)
    (hweak : ∀ t, 0 ≤ t → ∀ ℓ : F →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u n t)) atTop (𝓝 (ℓ (uLim t))))
    {s : ℝ} (hs : 0 < s) (ℓ : F →L[ℝ] ℝ) :
    Tendsto (fun n => ℓ (halfLineLaplace (u n) s)) atTop
      (𝓝 (ℓ (halfLineLaplace uLim s))) := by
  sorry

end KVApproximation.Analysis
