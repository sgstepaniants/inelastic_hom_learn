module

public import KVApproximation.Analysis.PeriodicDivergenceFourier
public import KVApproximation.Analysis.PeriodicFourierSynthesis
public import KVApproximation.Analysis.PeriodicRescalingLp
public import KVApproximation.Analysis.DivergenceTests

/-!
# Rescaling divergence-free periodic fields

Each Fourier mode has zero physical divergence. Continuous L² pullback
and unconditional Fourier synthesis extend its Dirichlet test identity
to the original periodic field.
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ENNReal

namespace KVApproximation.Analysis

private theorem rescaled_mode_divergence {d : ℕ} (n : Fin d → ℤ) (a : Fin d → ℂ)
    (ha : (∑ j, (n j : ℂ) * a j) = 0) (ε : ℝ) (x : PhysicalSpace d) :
    (∑ j, (fderiv ℝ (rescalePeriodic (realFourierMode n a) ε) x
      (EuclideanSpace.single j 1)) j) = 0 := by
  let L : PhysicalSpace d →L[ℝ] PhysicalSpace d := ε⁻¹ • ContinuousLinearMap.id ℝ _
  have hd := (((contDiff_realFourierMode_lift n a).differentiable (by simp)
    (ε⁻¹ • x)).hasFDerivAt).comp x L.hasFDerivAt
  change HasFDerivAt (rescalePeriodic (realFourierMode n a) ε)
    ((fderiv ℝ (fun z : PhysicalSpace d => realFourierMode n a (toCell z))
      (ε⁻¹ • x)).comp L) x at hd
  rw [hd.fderiv]
  change (∑ j, (fderiv ℝ (fun z : PhysicalSpace d => realFourierMode n a (toCell z))
    (ε⁻¹ • x) (ε⁻¹ • EuclideanSpace.single j 1)) j) = 0
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul]
  change (∑ j, ε⁻¹ * (fderiv ℝ
    (fun z : PhysicalSpace d => realFourierMode n a (toCell z))
      (ε⁻¹ • x) (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) j) = 0
  simp_rw [fderiv_realFourierMode_lift_apply]
  rw [← Finset.mul_sum]
  have hs : (∑ j, a j * (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
      UnitAddTorus.mFourier n (toCell (ε⁻¹ • x))) = 0 := by
    calc
      _ = (2 * (Real.pi : ℂ) * Complex.I * UnitAddTorus.mFourier n (toCell (ε⁻¹ • x))) *
          ∑ j, (n j : ℂ) * a j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [ha, mul_zero]
  have hr := congrArg Complex.reCLM hs
  rw [map_sum, map_zero] at hr
  simp only [Complex.reCLM_apply] at hr
  rw [hr, mul_zero]

/-- Theorem 3.1, static flux tests: periodic zero divergence is
preserved by physical rescaling and holds against every scalar Dirichlet test. -/
theorem HasPeriodicZeroDivergence.integral_rescale_gradient_eq_zero {d : ℕ}
    {q : Lp (PhysicalSpace d) 2 (cellMeasure d)} (h : HasPeriodicZeroDivergence q)
    {Ω : Opens (PhysicalSpace d)} (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (v : TauCeti.W1p volume Ω 2) (hv : v ∈ TauCeti.w1p0Submodule volume Ω 2) :
    (∫ x in (Ω : Set (PhysicalSpace d)),
      ⟪rescalePeriodic q ε x, TauCeti.W1p.gradient v x⟫_ℝ) = 0 := by
  obtain ⟨C, _, hbound⟩ := exists_rescaling_measure_bound hΩ
  have hscaled := (quasiMeasurePreserving_scaledToCell (d := d) hε.ne').measurable
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  let R : Lp (PhysicalSpace d) 2 (cellMeasure d) →L[ℝ] Lp (PhysicalSpace d) 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ _
      (hscaled.measurePreserving μ)).toContinuousLinearMap.comp
        (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (hbound ε hε hε₁))
  have hR (w : Lp (PhysicalSpace d) 2 (cellMeasure d)) :
      R w =ᵐ[μ] rescalePeriodic w ε := by
    exact (Lp.coeFn_compMeasurePreserving
      (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (hbound ε hε hε₁) w)
      (hscaled.measurePreserving μ)).trans
        ((hscaled.measurePreserving μ).quasiMeasurePreserving.ae
          (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (hbound ε hε hε₁) w))
  let L := (innerSL ℝ (TauCeti.W1p.gradient v)).comp R
  have hL (w : Lp (PhysicalSpace d) 2 (cellMeasure d)) :
      L w = ∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪rescalePeriodic w ε x, TauCeti.W1p.gradient v x⟫_ℝ := by
    change ⟪TauCeti.W1p.gradient v, R w⟫_ℝ = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hR w] with x hx
    rw [hx, real_inner_comm]
  let a (n : Fin d → ℤ) (j : Fin d) :=
    ∫ y, UnitAddTorus.mFourier (-n) y * (q y j : ℂ) ∂cellMeasure d
  have hmode (n : Fin d → ℤ) :
      L ((realFourierMode n (a n)).toLp 2 (cellMeasure d) ℝ) = 0 := by
    rw [hL]
    have hm : MemLp (realFourierMode n (a n)) 2 (cellMeasure d) :=
      (realFourierMode n (a n)).continuous.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hc : ContDiff ℝ 1 (rescalePeriodic (realFourierMode n (a n)) ε) :=
      ((contDiff_realFourierMode_lift n (a n)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ (PhysicalSpace d)).contDiff).of_le (by simp)
    have hi := integral_inner_gradient_eq_zero_of_divergence_eq_zero hc
      (memLp_two_rescalePeriodic hΩ hε hε₁ hm)
      (fun x _ => rescaled_mode_divergence n (a n) (h.fourier_coefficient n) ε x) v hv
    have heq : ∀ᵐ x ∂μ,
        rescalePeriodic ((realFourierMode n (a n)).toLp 2 (cellMeasure d) ℝ) ε x =
          rescalePeriodic (realFourierMode n (a n)) ε x :=
      ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hε.ne').ae
        ((realFourierMode n (a n)).coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d)))
    calc
      _ = ∫ x in (Ω : Set (PhysicalSpace d)),
          ⟪rescalePeriodic (realFourierMode n (a n)) ε x, TauCeti.W1p.gradient v x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [heq] with x hx
        rw [hx]
      _ = 0 := hi
  have hs := L.hasSum (hasSum_realFourier_series q)
  have hz : HasSum (fun n => L ((realFourierMode n (a n)).toLp 2 (cellMeasure d) ℝ)) 0 := by
    simpa only [hmode] using (hasSum_zero : HasSum (fun _ : Fin d → ℤ => (0 : ℝ)) 0)
  exact (hL q).symm.trans (hs.unique hz)

end KVApproximation.Analysis
