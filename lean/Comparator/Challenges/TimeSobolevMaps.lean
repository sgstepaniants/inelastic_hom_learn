module

public import KVApproximation.Analysis.TimeSobolev

/-!
# Bounded linear maps on time-Sobolev trajectories
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Appendix A.3: the time-Sobolev element is determined by its a.e. values. -/
theorem TimeH1.eq_of_value_ae {T : ℝ} {u v : TimeH1 H T}
    (h : TimeH1.value u =ᵐ[volume.restrict (Set.Ioo 0 T)] TimeH1.value v) : u = v := by
  sorry

/-- Appendix A.3: a bounded linear spatial map acts on both the value
and weak derivative of a finite-time H¹ trajectory. -/
theorem TimeH1.exists_map (A : H →L[ℝ] F) {T : ℝ} (u : TimeH1 H T) :
    ∃ v : TimeH1 F T,
      (TimeH1.value v =ᵐ[volume.restrict (Set.Ioo 0 T)] fun t => A (TimeH1.value u t)) ∧
      TimeH1.velocity v =ᵐ[volume.restrict (Set.Ioo 0 T)] fun t => A (TimeH1.velocity u t) := by
  sorry

/-- Appendix A.3: the same spatial map transports the continuous traces,
including the initial value. -/
theorem TimeH1.trace_map_of_value_ae (A : H →L[ℝ] F) {T : ℝ} (hT : 0 < T)
    (u : TimeH1 H T) (v : TimeH1 F T)
    (h : TimeH1.value v =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => A (TimeH1.value u t)) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT v t = A (TimeH1.trace hT u t) := by
  sorry

end KVApproximation.Analysis
