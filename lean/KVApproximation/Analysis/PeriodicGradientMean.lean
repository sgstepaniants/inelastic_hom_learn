module

public import KVApproximation.Analysis.PeriodicIntegration
public import KVApproximation.Analysis.PeriodicSobolev
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Mean of a periodic Sobolev gradient
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

private def gradientAverageL (d : ℕ) : PeriodicJetField d →L[ℝ] SecondOrder d :=
  ((ContinuousLinearMap.lsmul ℝ ℝ (E := SecondOrder d)).lpPairing
    (cellMeasure d) 2 2 (Lp.const 2 (cellMeasure d) (1 : ℝ))).comp
      ((WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).compLpL
        2 (cellMeasure d))

private theorem gradientAverageL_eq_integral {d : ℕ} (u : PeriodicJetField d) :
    gradientAverageL d u =
      ∫ y, (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)) (u y)
        ∂cellMeasure d := by
  rw [gradientAverageL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (cellMeasure d) (1 : ℝ),
    (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL u]
      with y hc hg
  change (Lp.const 2 (cellMeasure d) (1 : ℝ)) y •
    (((WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).compLpL
      2 (cellMeasure d)) u) y =
    (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)) (u y)
  rw [hc, Function.const_apply, one_smul, hg]

private theorem gradientAverageL_smooth {d : ℕ} {u : PeriodicJetField d}
    (hu : u ∈ smoothPeriodicJets d) : gradientAverageL d u = 0 := by
  obtain ⟨φ, hφ, hu⟩ := hu
  let ψ : PeriodicC1 d (EuclideanSpace ℝ (Fin d)) :=
    ⟨φ, hφ.of_le (by simp)⟩
  have hg : Continuous (periodicGradient φ) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin d × Fin d => ℝ)).comp
    apply continuous_pi
    intro ij
    exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) ij.1).comp
      (ψ.continuous_partial ij.2)
  have hgi : Integrable (periodicGradient φ) (cellMeasure d) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [gradientAverageL_eq_integral]
  have heq : (∫ y,
      (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)) (u y)
        ∂cellMeasure d) = ∫ y, periodicGradient φ y ∂cellMeasure d := by
    apply integral_congr_ae
    filter_upwards [hu] with y hy
    rw [hy]
    rfl
  rw [heq]
  apply PiLp.ext
  intro ij
  have hj := ψ.integral_partial_eq_zero ij.2
  have hji := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z ij.1) hj
  have hpint : Integrable (ψ.partial ij.2) (cellMeasure d) :=
    (ψ.continuous_partial ij.2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hproj := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) ij.1).integral_comp_comm hpint
  have hprojg := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d × Fin d => ℝ) ij).integral_comp_comm hgi
  change (∫ y, periodicGradient φ y ∂cellMeasure d) ij = 0
  change (∫ y, (ψ.partial ij.2 y) ij.1 ∂cellMeasure d) =
    (∫ y, ψ.partial ij.2 y ∂cellMeasure d) ij.1 at hproj
  change (∫ y, periodicGradient φ y ij ∂cellMeasure d) =
    (∫ y, periodicGradient φ y ∂cellMeasure d) ij at hprojg
  rw [← hprojg]
  exact hproj.trans hji

/-- Section 3.1: every periodic Sobolev gradient has mean zero. -/
theorem PeriodicH1.integral_gradient_eq_zero {d : ℕ} (u : PeriodicH1 d) :
    (∫ y, PeriodicH1.gradientL d u y ∂cellMeasure d) = 0 := by
  let K : ClosedSubmodule ℝ (PeriodicJetField d) :=
    (⊥ : ClosedSubmodule ℝ (SecondOrder d)).comap (gradientAverageL d)
  have hle : periodicH1Submodule d ≤ K := by
    apply Submodule.closure_le.mpr
    apply Submodule.span_le.mpr
    intro v hv
    exact gradientAverageL_smooth hv
  have hu : gradientAverageL d u.val = 0 := hle u.property
  rw [gradientAverageL_eq_integral] at hu
  rw [← hu]
  apply integral_congr_ae
  exact (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL u.val

end KVApproximation.Analysis
