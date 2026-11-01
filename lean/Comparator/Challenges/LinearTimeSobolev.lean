module

public import KVApproximation.Analysis.TimeSobolev
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Linear evolution with square-integrable forcing
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.Dynamics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.3 (`eq:cell_ode`): a bounded linear evolution equation with
square-integrable forcing has a unique finite-time H¹ solution. -/
theorem linear_timeH1_exists_unique (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    (f : ℝ → H) (hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T))) (q₀ : H) :
    ∃! u : TimeH1 H T,
      TimeH1.initial hT u = q₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity u t = A (TimeH1.value u t) + f t := by
  sorry

/-- Appendix A.3 (`eq:eta_sol`): variation of constants for a bounded
linear operator, valid at both endpoints for the continuous time trace. -/
theorem linear_timeH1_duhamel (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    (f : ℝ → H) (hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T)))
    (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t)
    (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT u t =
      (NormedSpace.exp ((t : ℝ) • A)) (TimeH1.initial hT u) +
        ∫ s in (0 : ℝ)..(t : ℝ), (NormedSpace.exp (((t : ℝ) - s) • A)) (f s) := by
  sorry

end KVApproximation.Dynamics
