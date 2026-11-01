module

public import KVApproximation.NeuralOperators.FourierProjectionApproximation
public import KVApproximation.Analysis.UniformLocalAverage
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Finite Fourier observations of compact continuous families

A common local average approximates a fixed evaluation. Approximating its
real L² kernel gives one finite Fourier projection for the whole family.
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, representatives: a finite Fourier observation depends only
on the almost-everywhere class of its input field. -/
private theorem projection_eval_congr_ae {d input output : ℕ}
    (Q : FourierProjection d input output)
    {h g : PeriodicCell d → Channels input} (hfg : h =ᵐ[cellMeasure d] g) :
    Q.eval h = Q.eval g := by
  have hc (k : Fin d → ℤ) (j : Fin input) :
      channelFourier h k j = channelFourier g k j := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  simp only [FourierProjection.eval, FourierProjection.complexValue, hc]

/-- Remark 4.3, compact-family observation: one finite Fourier projection
approximates evaluation uniformly on a jointly continuous compact family. -/
theorem exists_fourierProjection_approx_eval
    {P : Type*} [TopologicalSpace P] [CompactSpace P] {d n : ℕ}
    (F : C(P × PeriodicCell d, Channels n)) (y₀ : PeriodicCell d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : FourierProjection d n n, ∀ p : P,
      ‖Q.eval (fun y => F (p, y)) - F (p, y₀)‖ < ε := by
  let : Measure.IsOpenPosMeasure (cellMeasure d) := by
    unfold cellMeasure
    infer_instance
  obtain ⟨r, hr, hmass, havg⟩ :=
    exists_uniform_local_average (cellMeasure d) F y₀ (half_pos hε)
  let s := Metric.ball y₀ r
  have hs : MeasurableSet s := measurableSet_ball
  let mass := (cellMeasure d).real s
  let kfun : PeriodicCell d → ℝ := s.indicator (fun _ => mass⁻¹)
  have hkfun : MemLp kfun 2 (cellMeasure d) :=
    MemLp.indicator hs.nullMeasurableSet (memLp_const mass⁻¹)
  let κ : Lp ℝ 2 (cellMeasure d) := hkfun.toLp kfun
  let L : C(PeriodicCell d, Channels n) →L[ℝ] ChannelField d n :=
    ContinuousMap.toLp 2 (cellMeasure d) ℝ
  let H : C(P, ChannelField d n) :=
    ⟨fun p => L (F.curry p), L.continuous.comp F.curry.continuous⟩
  have hH (p : P) : H p =ᵐ[cellMeasure d] fun y => F (p, y) :=
    ContinuousMap.coeFn_toLp (cellMeasure d) (F.curry p)
  have hint (p : P) : Integrable (fun y => F (p, y)) (cellMeasure d) :=
    (F.curry p).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hkernel (p : P) :
      (∫ y, κ y • H p y ∂cellMeasure d) =
        mass⁻¹ • (∫ y in s, F (p, y) ∂cellMeasure d) := by
    calc
      _ = ∫ y, s.indicator (fun y => mass⁻¹ • F (p, y)) y ∂cellMeasure d := by
        apply integral_congr_ae
        filter_upwards [hkfun.coeFn_toLp, hH p] with y hk hy
        change (hkfun.toLp kfun) y • H p y = _
        rw [hk, hy]
        by_cases hys : y ∈ s <;> simp [kfun, hys]
      _ = ∫ y in s, mass⁻¹ • F (p, y) ∂cellMeasure d := integral_indicator hs
      _ = mass⁻¹ • (∫ y in s, F (p, y) ∂cellMeasure d) :=
        (mass⁻¹ • ContinuousLinearMap.id ℝ (Channels n)).integral_comp_comm
          (hint p).restrict
  let η := (ε / 2) / (‖H‖ + 1)
  have hden : 0 < ‖H‖ + 1 := by positivity
  have hη : 0 < η := div_pos (half_pos hε) hden
  obtain ⟨Q, hQ⟩ := exists_fourierProjection_approx_integral κ hη
  have hbudget : η * ‖H‖ ≤ ε / 2 := calc
    η * ‖H‖ ≤ η * (‖H‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
    _ = ε / 2 := div_mul_cancel₀ (ε / 2) hden.ne'
  refine ⟨Q, fun p => ?_⟩
  have hproj : ‖Q.eval (fun y => F (p, y)) -
      mass⁻¹ • (∫ y in s, F (p, y) ∂cellMeasure d)‖ ≤ ε / 2 := by
    have hp := hQ (H p)
    rw [projection_eval_congr_ae Q (hH p), hkernel p] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_left (H.norm_coe_le_norm p) hη.le).trans hbudget)
  calc
    _ ≤ ‖Q.eval (fun y => F (p, y)) -
          mass⁻¹ • (∫ y in s, F (p, y) ∂cellMeasure d)‖ +
        ‖mass⁻¹ • (∫ y in s, F (p, y) ∂cellMeasure d) - F (p, y₀)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hproj (havg p)
    _ = ε := add_halves ε

end KVApproximation.NeuralOperators
