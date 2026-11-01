module

public import KVApproximation.Analysis.TimeSobolev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Hilbert-valued time derivatives and continuous traces
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1 and Appendix A.3: the finite-time value representative lies in L². -/
theorem TimeH1.value_memLp {T : ℝ} (u : TimeH1 H T) :
    MemLp (TimeH1.value u) 2 (volume.restrict (Set.Ioo 0 T)) := by
  sorry

/-- Theorem 3.1 and Appendix A.3: the Hilbert-valued time derivative lies in L². -/
theorem TimeH1.velocity_memLp {T : ℝ} (u : TimeH1 H T) :
    MemLp (TimeH1.velocity u) 2 (volume.restrict (Set.Ioo 0 T)) := by
  sorry

/-- Appendix A.3: the inverse Riesz identification recovers the ordinary
Hilbert-valued weak derivative. -/
theorem TimeH1.hasWeakLineDerivOn {T : ℝ} (u : TimeH1 H T) :
    TauCeti.HasWeakLineDerivOn volume ⟨Set.Ioo 0 T, isOpen_Ioo⟩
      (TimeH1.value u) (TimeH1.velocity u) 1 := by
  sorry

/-- Theorem 3.1 and Appendix A.3: the closed-interval trace agrees with
the value representative almost everywhere on the open interval. -/
theorem TimeH1.trace_ae {T : ℝ} (hT : 0 < T) (u : TimeH1 H T) :
    TimeH1.value u =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => TimeH1.trace hT u (Set.projIcc 0 T hT.le t) := by
  sorry

/-- Appendix A.3, time integration in `eq:eta_sol`: the continuous trace
is the initial value plus the integral of the weak derivative at every time. -/
theorem TimeH1.trace_integral {T : ℝ} (hT : 0 < T) (u : TimeH1 H T)
    (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT u t = TimeH1.initial hT u +
      ∫ s in (0 : ℝ)..(t : ℝ), TimeH1.velocity u s := by
  sorry

/-- Appendix A.3: a Hilbert-valued L² function with an L² weak derivative
defines an element of the finite-time H¹ space. -/
theorem TimeH1.exists_of_weak_derivative {T : ℝ} {u v : ℝ → H}
    (hu : MemLp u 2 (volume.restrict (Set.Ioo 0 T)))
    (hv : MemLp v 2 (volume.restrict (Set.Ioo 0 T)))
    (hweak : TauCeti.HasWeakLineDerivOn volume ⟨Set.Ioo 0 T, isOpen_Ioo⟩ u v 1) :
    ∃ w : TimeH1 H T,
      TimeH1.value w =ᵐ[volume.restrict (Set.Ioo 0 T)] u ∧
      TimeH1.velocity w =ᵐ[volume.restrict (Set.Ioo 0 T)] v := by
  sorry

end KVApproximation.Analysis
