module

public import KVApproximation.Analysis.TimeSobolev
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval

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
  exact Lp.memLp (TauCeti.EvolutionSpace.value u)

/-- Theorem 3.1 and Appendix A.3: the Hilbert-valued time derivative lies in L². -/
theorem TimeH1.velocity_memLp {T : ℝ} (u : TimeH1 H T) :
    MemLp (TimeH1.velocity u) 2 (volume.restrict (Set.Ioo 0 T)) := by
  exact (Lp.memLp (TauCeti.EvolutionSpace.timeDeriv u)).continuousLinearMap_comp
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Appendix A.3: the identity-pivot dual embedding is the Riesz isometry. -/
private theorem identity_gelfandDual :
    (ContinuousLinearMap.id ℝ H).gelfandDual =
      (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap := by
  ext x y
  simp

/-- Appendix A.3: the inverse Riesz identification recovers the ordinary
Hilbert-valued weak derivative. -/
theorem TimeH1.hasWeakLineDerivOn {T : ℝ} (u : TimeH1 H T) :
    TauCeti.HasWeakLineDerivOn volume ⟨Set.Ioo 0 T, isOpen_Ioo⟩
      (TimeH1.value u) (TimeH1.velocity u) 1 := by
  let D := (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have h := (TauCeti.EvolutionSpace.hasWeakLineDerivOn u).clm_comp D
  have heq : (fun t => D ((ContinuousLinearMap.id ℝ H).gelfandDual
      ((ContinuousLinearMap.id ℝ H) (TauCeti.EvolutionSpace.value u t)))) =
        TimeH1.value u := by
    funext t
    rw [identity_gelfandDual]
    exact (InnerProductSpace.toDual ℝ H).symm_apply_apply _
  rw [heq] at h
  exact h

/-- Theorem 3.1 and Appendix A.3: the closed-interval trace agrees with
the value representative almost everywhere on the open interval. -/
theorem TimeH1.trace_ae {T : ℝ} (hT : 0 < T) (u : TimeH1 H T) :
    TimeH1.value u =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => TimeH1.trace hT u (Set.projIcc 0 T hT.le t) := by
  change (fun t => TauCeti.EvolutionSpace.value u t) =ᵐ[volume.restrict (Set.Ioo 0 T)]
    fun t => TauCeti.EvolutionSpace.toContinuousMap hT u (Set.projIcc 0 T hT.le t)
  exact TauCeti.EvolutionSpace.value_ae_eq_toContinuousMap
    (ι := ContinuousLinearMap.id ℝ H) hT u

/-- Appendix A.3, time integration in `eq:eta_sol`: the continuous trace
is the initial value plus the integral of the weak derivative at every time. -/
theorem TimeH1.trace_integral {T : ℝ} (hT : 0 < T) (u : TimeH1 H T)
    (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT u t = TimeH1.initial hT u +
      ∫ s in (0 : ℝ)..(t : ℝ), TimeH1.velocity u s := by
  have hint : IntegrableOn (TimeH1.velocity u) (Set.Ioo 0 T) :=
    (TimeH1.velocity_memLp u).integrable (by norm_num)
  have h := (TimeH1.hasWeakLineDerivOn u).integral_eq_sub hint
    ((TimeH1.trace hT u).continuous.comp continuous_projIcc).continuousOn
    (TimeH1.trace_ae hT u) (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT.le⟩) t.property
  have hi : (∫ s in (0 : ℝ)..(t : ℝ), TimeH1.velocity u s) =
      TimeH1.trace hT u t - TimeH1.initial hT u := by
    simpa only [Function.comp_apply, Set.projIcc_of_mem hT.le t.property,
      Set.projIcc_of_mem hT.le (show (0 : ℝ) ∈ Set.Icc 0 T from ⟨le_rfl, hT.le⟩),
      TimeH1.initial] using h
  calc
    TimeH1.trace hT u t = (TimeH1.trace hT u t - TimeH1.initial hT u) +
        TimeH1.initial hT u := by abel
    _ = _ := by rw [← hi]; abel

/-- Appendix A.3: a Hilbert-valued L² function with an L² weak derivative
defines an element of the finite-time H¹ space. -/
theorem TimeH1.exists_of_weak_derivative {T : ℝ} {u v : ℝ → H}
    (hu : MemLp u 2 (volume.restrict (Set.Ioo 0 T)))
    (hv : MemLp v 2 (volume.restrict (Set.Ioo 0 T)))
    (hweak : TauCeti.HasWeakLineDerivOn volume ⟨Set.Ioo 0 T, isOpen_Ioo⟩ u v 1) :
    ∃ w : TimeH1 H T,
      TimeH1.value w =ᵐ[volume.restrict (Set.Ioo 0 T)] u ∧
      TimeH1.velocity w =ᵐ[volume.restrict (Set.Ioo 0 T)] v := by
  let L := (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  let uLp := hu.toLp u
  let vLp := L.compLp (hv.toLp v)
  have huv : (uLp : ℝ → H) =ᵐ[volume.restrict (Set.Ioo 0 T)] u := hu.coeFn_toLp
  have hvv : (vLp : ℝ → StrongDual ℝ H) =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun t => L (v t) := by
    filter_upwards [L.coeFn_compLp (hv.toLp v), hv.coeFn_toLp] with t ht hs
    exact ht.trans (congrArg L hs)
  have hweak' : TauCeti.HasWeakLineDerivOn volume ⟨Set.Ioo 0 T, isOpen_Ioo⟩
      (fun t => (ContinuousLinearMap.id ℝ H).gelfandDual
        ((ContinuousLinearMap.id ℝ H) (uLp t))) vLp 1 := by
    rw [identity_gelfandDual]
    apply ((hweak.clm_comp L).congr_ae ?_).congr_ae_deriv hvv.symm
    filter_upwards [huv] with t ht
    exact congrArg L ht.symm
  let w : TimeH1 H T := TauCeti.EvolutionSpace.mk uLp vLp hweak'
  refine ⟨w, ?_, ?_⟩
  · change (fun t => TauCeti.EvolutionSpace.value
      (TauCeti.EvolutionSpace.mk uLp vLp hweak') t) =ᵐ[volume.restrict (Set.Ioo 0 T)] u
    rw [TauCeti.EvolutionSpace.value_mk]
    exact huv
  · change (fun t => (InnerProductSpace.toDual ℝ H).symm
      (TauCeti.EvolutionSpace.timeDeriv (TauCeti.EvolutionSpace.mk uLp vLp hweak') t))
        =ᵐ[volume.restrict (Set.Ioo 0 T)] v
    rw [TauCeti.EvolutionSpace.timeDeriv_mk]
    filter_upwards [hvv] with t ht
    rw [ht]
    exact (InnerProductSpace.toDual ℝ H).symm_apply_apply _

end KVApproximation.Analysis
