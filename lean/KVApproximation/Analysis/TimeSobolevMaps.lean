module

public import KVApproximation.Analysis.TimeSobolevProperties

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
  apply TauCeti.EvolutionSpace.ext
  exact Lp.ext h

/-- Appendix A.3: a bounded linear spatial map acts on both the value
and weak derivative of a finite-time H¹ trajectory. -/
theorem TimeH1.exists_map (A : H →L[ℝ] F) {T : ℝ} (u : TimeH1 H T) :
    ∃ v : TimeH1 F T,
      (TimeH1.value v =ᵐ[volume.restrict (Set.Ioo 0 T)] fun t => A (TimeH1.value u t)) ∧
      TimeH1.velocity v =ᵐ[volume.restrict (Set.Ioo 0 T)] fun t => A (TimeH1.velocity u t) := by
  exact TimeH1.exists_of_weak_derivative
    ((TimeH1.value_memLp u).continuousLinearMap_comp A)
    ((TimeH1.velocity_memLp u).continuousLinearMap_comp A)
    ((TimeH1.hasWeakLineDerivOn u).clm_comp A)

/-- Appendix A.3: the same spatial map transports the continuous traces,
including the initial value. -/
theorem TimeH1.trace_map_of_value_ae (A : H →L[ℝ] F) {T : ℝ} (hT : 0 < T)
    (u : TimeH1 H T) (v : TimeH1 F T)
    (h : TimeH1.value v =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => A (TimeH1.value u t)) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT v t = A (TimeH1.trace hT u t) := by
  have hae : (fun s => TimeH1.trace hT v (Set.projIcc 0 T hT.le s))
      =ᵐ[volume.restrict (Set.Icc 0 T)]
        fun s => A (TimeH1.trace hT u (Set.projIcc 0 T hT.le s)) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [TimeH1.trace_ae hT v, h, TimeH1.trace_ae hT u] with s hvs hs hus
    exact hvs.symm.trans (hs.trans (congrArg A hus))
  have heq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) hae
    ((TimeH1.trace hT v).continuous.comp continuous_projIcc).continuousOn
    (A.continuous.comp ((TimeH1.trace hT u).continuous.comp continuous_projIcc)).continuousOn
  simpa only [Set.projIcc_of_mem hT.le t.property] using heq t.property

end KVApproximation.Analysis
