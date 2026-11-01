module

public import KVApproximation.Analysis.PeriodicFourierMode
public import KVApproximation.Analysis.PeriodicFourier
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Smooth real Fourier synthesis
-/

public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

private def realAmplitudeL {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    ℂ →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      Complex.reCLM.comp (a i • ContinuousLinearMap.id ℝ ℂ))

/-- Section 3.1, smooth density argument: every real Fourier mode has a
smooth periodic Euclidean lift. -/
theorem contDiff_realFourierMode_lift {d : ℕ} {ι : Type*} [Fintype ι]
    (n : Fin d → ℤ) (a : ι → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => realFourierMode n a (toCell x)) := by
  exact (realAmplitudeL a).contDiff.comp (contDiff_mFourier_lift n)

/-- Section 3.1, smooth density argument: the coordinate derivative of a
real Fourier mode retains the exact unit-torus multiplier. -/
theorem fderiv_realFourierMode_lift_apply {d : ℕ} {ι : Type*} [Fintype ι]
    (n : Fin d → ℤ) (a : ι → ℂ) (x : EuclideanSpace ℝ (Fin d))
    (i : ι) (j : Fin d) :
    (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => realFourierMode n a (toCell z)) x
      (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) i =
      (a i * (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
        UnitAddTorus.mFourier n (toCell x)).re := by
  have hd := (realAmplitudeL a).hasFDerivAt.comp x
    ((contDiff_mFourier_lift n).differentiable (by simp) x).hasFDerivAt
  change HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => realFourierMode n a (toCell z))
    ((realAmplitudeL a).comp
      (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => UnitAddTorus.mFourier n (toCell z)) x)) x at hd
  rw [hd.fderiv]
  change (a i * fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) =>
    UnitAddTorus.mFourier n (toCell z)) x (WithLp.toLp 2 (Pi.single j (1 : ℝ)))).re = _
  rw [fderiv_mFourier_lift_apply]
  exact congrArg Complex.re (mul_assoc _ _ _).symm

/-- Section 3.1, smooth density argument: real parts of the complex Fourier
series converge in the actual Euclidean L² norm. -/
theorem hasSum_realFourier_series {d : ℕ} {ι : Type*} [Fintype ι]
    (f : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d)) :
    HasSum (fun n : Fin d → ℤ =>
      (realFourierMode n (fun i =>
        ∫ y, UnitAddTorus.mFourier (-n) y * (f y i : ℂ) ∂cellMeasure d)).toLp
        2 (cellMeasure d) ℝ) f := by
  classical
  let C (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : ι => ℝ) i)
  let F (i : ι) : Lp ℂ 2 (cellMeasure d) := (C i).compLpL 2 (cellMeasure d) f
  let E (i : ι) : ℂ →L[ℝ] EuclideanSpace ℝ ι :=
    Complex.reCLM.smulRight (EuclideanSpace.single i (1 : ℝ))
  let T (i : ι) := (E i).compLpL 2 (cellMeasure d)
  let b : (Fin d → ℤ) → Lp ℂ 2 (cellMeasure d) := fun n => UnitAddTorus.mFourierLp 2 n
  have hsingle (i : ι) :
      HasSum (fun n : Fin d → ℤ => T i
        (UnitAddTorus.mFourierCoeff (F i) n • b n)) (T i (F i)) :=
    (T i).hasSum (UnitAddTorus.hasSum_mFourier_series_L2 (F i))
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hsingle i)
  have hcoord (i : ι) : ∀ᵐ y ∂cellMeasure d,
      T i (F i) y = f y i • EuclideanSpace.single i (1 : ℝ) := by
    filter_upwards [(E i).coeFn_compLpL (F i), (C i).coeFn_compLpL f] with y he hc
    change ((E i).compLpL 2 (cellMeasure d) (F i)) y = _
    rw [he]
    change (F i y).re • EuclideanSpace.single i (1 : ℝ) = _
    change F i y = C i (f y) at hc
    rw [hc]
    rfl
  have hlim : (∑ i, T i (F i)) = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => T i (F i)),
      ae_all_iff.mpr hcoord] with y hy hc
    rw [hy]
    simp_rw [hc]
    apply PiLp.ext
    intro k
    simp [WithLp.ofLp_sum, Pi.single_apply, apply_ite]
  rw [hlim] at hsum
  apply hsum.congr_fun
  intro n
  let a : ι → ℂ := fun i =>
    ∫ y, UnitAddTorus.mFourier (-n) y * (f y i : ℂ) ∂cellMeasure d
  have hc (i : ι) : UnitAddTorus.mFourierCoeff (F i) n = a i := by
    apply integral_congr_ae
    filter_upwards [(C i).coeFn_compLpL f] with y hy
    change UnitAddTorus.mFourier (-n) y * ((C i).compLpL 2 (cellMeasure d) f) y = _
    rw [hy]
    rfl
  simp_rw [hc]
  have hb : ∀ᵐ y ∂cellMeasure d, b n y = UnitAddTorus.mFourier n y :=
    UnitAddTorus.coeFn_mFourierLp 2 n
  have hterm (i : ι) : ∀ᵐ y ∂cellMeasure d,
      T i (a i • b n) y =
        (a i * UnitAddTorus.mFourier n y).re • EuclideanSpace.single i (1 : ℝ) := by
    filter_upwards [(E i).coeFn_compLpL (a i • b n),
      Lp.coeFn_smul (a i) (b n),
      hb] with y he hs hb
    change ((E i).compLpL 2 (cellMeasure d) (a i • b n)) y = _
    rw [he]
    change ((a i • b n) y).re • EuclideanSpace.single i (1 : ℝ) = _
    rw [hs]
    change (a i * b n y).re • EuclideanSpace.single i (1 : ℝ) = _
    rw [hb]
  apply Lp.ext
  filter_upwards [(realFourierMode n a).coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i => T i (a i • b n)),
    ae_all_iff.mpr hterm] with y hy hs ht
  rw [hy, hs]
  simp_rw [ht]
  apply PiLp.ext
  intro k
  simp [realFourierMode, WithLp.ofLp_sum, Pi.single_apply, apply_ite]

end KVApproximation.Analysis
