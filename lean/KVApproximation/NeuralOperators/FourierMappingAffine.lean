module

public import KVApproximation.NeuralOperators.FourierMapping
public import KVApproximation.Analysis.PeriodicFourierFunctionals
public import KVApproximation.Analysis.PeriodicFourierMode
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Affine Fourier layers on L²
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1, synthesis ingredient: real and imaginary coefficient parts
multiply two fixed real Fourier fields, giving a continuous real-linear map. -/
private theorem exists_modeCLM {d output : ℕ} (k : Fin d → ℤ)
    (a : Fin output → ℂ) :
    ∃ S : ℂ →L[ℝ] ChannelField d output, ∀ z : ℂ,
      (S z : PeriodicCell d → Channels output) =ᵐ[cellMeasure d]
        fun y => realFourierMode k (fun i => a i * z) y := by
  let vr := realFourierMode k a
  let vi := realFourierMode k (fun i => a i * Complex.I)
  let r : ChannelField d output := vr.toLp 2 (cellMeasure d) ℝ
  let s : ChannelField d output := vi.toLp 2 (cellMeasure d) ℝ
  refine ⟨Complex.reCLM.smulRight r + Complex.imCLM.smulRight s, ?_⟩
  intro z
  change ((z.re • r + z.im • s : ChannelField d output) :
    PeriodicCell d → Channels output) =ᵐ[cellMeasure d] _
  filter_upwards [Lp.coeFn_add (z.re • r) (z.im • s),
    Lp.coeFn_smul z.re r, Lp.coeFn_smul z.im s,
    vr.coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d),
    vi.coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d)]
    with y hadd hr hi hvr hvi
  rw [hadd, Pi.add_apply, hr, hi, Pi.smul_apply, Pi.smul_apply, hvr, hvi]
  apply PiLp.ext
  intro i
  change z.re * (a i * UnitAddTorus.mFourier k y).re +
    z.im * ((a i * Complex.I) * UnitAddTorus.mFourier k y).re =
      ((a i * z) * UnitAddTorus.mFourier k y).re
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- Example 2.1 and Remark 4.3, affine stage: local channel weights,
finite Fourier synthesis and the stated constant bias define an actual affine L² map. -/
theorem FourierLayer.exists_affineCLM {d input output : ℕ}
    (L : FourierLayer d input output) :
    ∃ A : ChannelField d input →L[ℝ] ChannelField d output,
      ∃ b : ChannelField d output, ∀ h : ChannelField d input,
        ((A h + b : ChannelField d output) : PeriodicCell d → Channels output) =ᵐ[cellMeasure d]
          fun y => WithLp.toLp 2 (fun i =>
            (∑ j : Fin input, L.localWeight i j * h y j) +
              (L.fourierPart h y i).re + L.bias i) := by
  classical
  let W : Channels input →L[ℝ] Channels output :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin output => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => ∑ j : Fin input,
        L.localWeight i j • PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin input => ℝ) j)
  have hW (x : Channels input) (i : Fin output) :
      W x i = ∑ j : Fin input, L.localWeight i j * x j := by
    change (∑ j : Fin input,
      L.localWeight i j • PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin input => ℝ) j) x = _
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      PiLp.proj_apply, smul_eq_mul]
  let c (k : Fin d → ℤ) (j : Fin input) : ChannelField d input →L[ℝ] ℂ :=
    (exists_periodicFourierCoefficientCLM k j).choose
  have hc (k : Fin d → ℤ) (j : Fin input) (h : ChannelField d input) :
      c k j h = channelFourier h k j :=
    (exists_periodicFourierCoefficientCLM k j).choose_spec h
  let S (k : Fin d → ℤ) (j : Fin input) : ℂ →L[ℝ] ChannelField d output :=
    (exists_modeCLM k (fun i => L.multiplier k i j)).choose
  have hS (k : Fin d → ℤ) (j : Fin input) (z : ℂ) :
      (S k j z : PeriodicCell d → Channels output) =ᵐ[cellMeasure d]
        fun y => realFourierMode k (fun i => L.multiplier k i j * z) y :=
    (exists_modeCLM k (fun i => L.multiplier k i j)).choose_spec z
  let D (k : Fin d → ℤ) : ChannelField d input →L[ℝ] ChannelField d output :=
    ∑ j : Fin input, (S k j).comp (c k j)
  have hD (k : Fin d → ℤ) (h : ChannelField d input) :
      (D k h : PeriodicCell d → Channels output) =ᵐ[cellMeasure d]
        fun y => ∑ j : Fin input,
          realFourierMode k (fun i => L.multiplier k i j * channelFourier h k j) y := by
    simp only [D, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => S k j (c k j h)),
      ae_all_iff.mpr (fun j => hS k j (c k j h))] with y hsum hterms
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hterms j, hc]
  let F : ChannelField d input →L[ℝ] ChannelField d output :=
    ∑ k ∈ frequencyBox L.cutoff, D k
  have hF (h : ChannelField d input) :
      (F h : PeriodicCell d → Channels output) =ᵐ[cellMeasure d]
        fun y => ∑ k ∈ frequencyBox L.cutoff, ∑ j : Fin input,
          realFourierMode k (fun i => L.multiplier k i j * channelFourier h k j) y := by
    simp only [F, ContinuousLinearMap.sum_apply]
    filter_upwards [Lp.coeFn_fun_finsetSum (frequencyBox L.cutoff) (fun k => D k h),
      ae_all_iff.mpr (fun k => hD k h)] with y hsum hterms
    rw [hsum]
    exact Finset.sum_congr rfl (fun k hk => hterms k)
  let A : ChannelField d input →L[ℝ] ChannelField d output :=
    W.compLpL 2 (cellMeasure d) + F
  let bias : Channels output := WithLp.toLp 2 L.bias
  have hbias : MemLp (fun _ : PeriodicCell d => bias) 2 (cellMeasure d) := memLp_const _
  let b : ChannelField d output := hbias.toLp (fun _ : PeriodicCell d => bias)
  refine ⟨A, b, ?_⟩
  intro h
  have hA : (A h : PeriodicCell d → Channels output) =ᵐ[cellMeasure d]
      fun y => W (h y) + ∑ k ∈ frequencyBox L.cutoff, ∑ j : Fin input,
        realFourierMode k (fun i => L.multiplier k i j * channelFourier h k j) y := by
    change ((W.compLpL 2 (cellMeasure d) h + F h : ChannelField d output) :
      PeriodicCell d → Channels output) =ᵐ[cellMeasure d] _
    filter_upwards [Lp.coeFn_add (W.compLpL 2 (cellMeasure d) h) (F h),
      W.coeFn_compLpL h, hF h] with y hadd hlocal hfourier
    rw [hadd, Pi.add_apply, hlocal, hfourier]
  filter_upwards [Lp.coeFn_add (A h) b, hA, hbias.coeFn_toLp]
    with y hadd hlinear hconstant
  rw [hadd, Pi.add_apply, hlinear, hconstant]
  apply PiLp.ext
  intro i
  change W (h y) i +
    (∑ k ∈ frequencyBox L.cutoff, ∑ j : Fin input,
      realFourierMode k (fun i => L.multiplier k i j * channelFourier h k j) y) i +
        L.bias i = _
  rw [hW]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, realFourierMode,
    ContinuousMap.coe_mk, WithLp.ofLp_toLp, FourierLayer.fourierPart,
    Finset.sum_mul, Complex.re_sum]

end KVApproximation.NeuralOperators
