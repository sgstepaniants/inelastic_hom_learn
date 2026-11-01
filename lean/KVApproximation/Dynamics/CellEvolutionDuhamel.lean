module

public import KVApproximation.Dynamics.CellEvolutionAlgebra
public import KVApproximation.Dynamics.LinearTimeDuhamel

/-!
# The shifted cell corrector and its Duhamel formula
-/

public section

open MeasureTheory Set
open KVApproximation.Analysis KVApproximation.OperatorTheory

namespace KVApproximation.Dynamics

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Appendix A.3 (`eq:eta_sol`): variation of constants for the shifted corrector,
using its continuous trace at every time in the closed interval. -/
theorem cell_evolution_duhamel (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T)
    (η : TimeH1 X T) (hη : IsCellEvolution V E X ι hT e η)
    (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT η t + E.projection X (ι (TimeH1.trace hT e t)) =
      -(∫ s in (0 : ℝ)..(t : ℝ),
        relaxationSemigroup V E X (t - s) (mismatch V E X (ι (TimeH1.velocity e s)))) := by
  let L := (E.projection X).comp ι
  let D := (mismatch V E X).comp ι
  let R := relaxation V E X
  let q : ℝ → X := fun s => TimeH1.value η s + L (TimeH1.value e s)
  let v : ℝ → X := fun s => TimeH1.velocity η s + L (TimeH1.velocity e s)
  have hq : MemLp q 2 (volume.restrict (Ioo 0 T)) :=
    (TimeH1.value_memLp η).add ((TimeH1.value_memLp e).continuousLinearMap_comp L)
  have hv : MemLp v 2 (volume.restrict (Ioo 0 T)) :=
    (TimeH1.velocity_memLp η).add ((TimeH1.velocity_memLp e).continuousLinearMap_comp L)
  have hweak : TauCeti.HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩ q v 1 :=
    (TimeH1.hasWeakLineDerivOn η).add ((TimeH1.hasWeakLineDerivOn e).clm_comp L)
  obtain ⟨ω, hωq, hωv⟩ := TimeH1.exists_of_weak_derivative hq hv hweak
  have htr : (fun s => TimeH1.trace hT ω (projIcc 0 T hT.le s))
      =ᵐ[volume.restrict (Icc 0 T)]
        fun s => TimeH1.trace hT η (projIcc 0 T hT.le s) +
          L (TimeH1.trace hT e (projIcc 0 T hT.le s)) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [TimeH1.trace_ae hT ω, hωq, TimeH1.trace_ae hT η,
      TimeH1.trace_ae hT e] with s hωs hqs hηs hes
    rw [← hωs, hqs]
    change TimeH1.value η s + L (TimeH1.value e s) = _
    rw [hηs, hes]
  have heq := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) htr
    ((TimeH1.trace hT ω).continuous.comp continuous_projIcc).continuousOn
    (((TimeH1.trace hT η).continuous.comp continuous_projIcc).add
      (L.continuous.comp ((TimeH1.trace hT e).continuous.comp continuous_projIcc))).continuousOn
  have htrace (s : Icc (0 : ℝ) T) : TimeH1.trace hT ω s =
      TimeH1.trace hT η s + L (TimeH1.trace hT e s) := by
    simpa only [projIcc_of_mem hT.le s.property] using heq s.property
  have hshift := cell_evolution_shifted_ode V E X ι hT e η hη
  have hinit : TimeH1.initial hT ω = 0 := by
    change TimeH1.trace hT ω ⟨0, le_rfl, hT.le⟩ = 0
    rw [htrace]
    exact hshift.1
  have hforcing : MemLp (fun s => -D (TimeH1.velocity e s)) 2
      (volume.restrict (Ioo 0 T)) :=
    ((TimeH1.velocity_memLp e).continuousLinearMap_comp D).neg
  have hode : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      TimeH1.velocity ω s = (-R) (TimeH1.value ω s) + -D (TimeH1.velocity e s) := by
    filter_upwards [hωq, hωv, hshift.2] with s hqs hvs hs
    rw [hqs, hvs]
    change v s = -R (q s) + -D (TimeH1.velocity e s)
    change v s + R (q s) = -D (TimeH1.velocity e s) at hs
    calc
      v s = (v s + R (q s)) - R (q s) := by abel
      _ = _ := by rw [hs]; abel
  have h := linear_timeH1_duhamel (-R) hT
    (fun s => -D (TimeH1.velocity e s)) hforcing ω hode t
  rw [hinit, map_zero, zero_add, htrace] at h
  change TimeH1.trace hT η t + E.projection X (ι (TimeH1.trace hT e t)) = _ at h
  rw [h, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [map_neg]
  congr 1
  have hgen : ((t : ℝ) - s) • (-R) = (-((t : ℝ) - s)) • R := by
    exact (smul_neg ((t : ℝ) - s) R).trans (neg_smul ((t : ℝ) - s) R).symm
  rw [hgen]
  rfl

end KVApproximation.Dynamics
