module

public import KVApproximation.Approximation.RealResponseIdentities
public import KVApproximation.Spectral.TensorActionIntegration
public import KVApproximation.Spectral.TensorActionFubini

/-!
# The exact memory as a weighted-response integral
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Proposition B.10, proof: the exact memory convolution is integration
of the real weighted response against the resolvent-weighted measure. -/
theorem memory_eq_weightedResponseIntegral {d : ℕ} {lower upper c : ℝ}
    (hlower : 0 < lower) (hc : 0 < c) (ν : TensorMeasure d)
    (K : ℝ → Elasticity d) (hrep : IsSpectralRepresentation ν K lower upper)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, action (K (t - s)) (e.velocity s)) =
      tensorActionIntegral (weightedMeasure c ν) (realWeightedResponse c e t) := by
  let η := volume.restrict (Set.Ioc 0 t)
  let : IsFiniteMeasure η := ⟨by simp [η, Real.volume_Ioc]⟩
  let : IsFiniteMeasure ν.variation := ⟨hrep.2.2.1⟩
  let f (s r : ℝ) := (r * Real.exp (-r * (t - s))) • e.velocity s
  have hv : Integrable e.velocity η :=
    (e.velocity_intervalIntegrable le_rfl ht).1
  have hrect : ∀ᵐ p ∂η.prod ν.variation,
      p ∈ (Set.Ioc 0 t) ×ˢ (Set.Icc lower upper) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioc.prod measurableSet_Icc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    filter_upwards [ae_iff.mpr hrep.2.1] with r hr
    exact ⟨hs, hr⟩
  have hscalar : Continuous (fun p : ℝ × ℝ => p.2 * Real.exp (-p.2 * (t - p.1))) := by
    fun_prop
  have hbound : ∀ᵐ p ∂η.prod ν.variation,
      ‖p.2 * Real.exp (-p.2 * (t - p.1))‖ ≤ upper := by
    filter_upwards [hrect] with p hp
    have hrpos := hlower.trans_le hp.2.1
    have hts : 0 ≤ t - p.1 := sub_nonneg.mpr hp.1.2
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hrpos, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ p.2 * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrpos.le) hts))
        hrpos.le
      _ ≤ upper := by simpa only [mul_one] using hp.2.2
  have hproduct : Integrable (Function.uncurry f) (η.prod ν.variation) :=
    (hv.comp_fst ν.variation).bdd_smul upper hscalar.aestronglyMeasurable hbound
  have hsection (s : ℝ) : Integrable (fun r => r * Real.exp (-r * (t - s))) ν.variation :=
    ν.integrable_continuousOn hrep.2.2.1 hrep.2.1 _ (by fun_prop)
  rw [weightedMeasure_actionIntegral hlower hc ν hrep.1 hrep.2.1 hrep.2.2.1
    _ (continuous_realWeightedResponse c e ht).continuousOn,
    intervalIntegral.integral_of_le ht]
  calc
    _ = ∫ s, tensorActionIntegral ν (f s) ∂η := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [hrep.2.2.2 (t - s) (sub_nonneg.mpr hs.2)]
      exact (tensorActionIntegral_smul ν _ (hsection s) (e.velocity s)).symm
    _ = tensorActionIntegral ν (fun r => ∫ s, f s r ∂η) :=
      integral_tensorActionIntegral_swap η ν hrep.2.2.1 f hproduct
    _ = _ := by
      apply VectorMeasure.integral_congr_ae
      filter_upwards [ae_iff.mpr hrep.2.1] with r hr
      have hcr : c + r ≠ 0 := (add_pos hc (hlower.trans_le hr.1)).ne'
      rw [realWeightedResponse, smul_smul, resolventWeight, div_mul_cancel₀ _ hcr,
        dampedResponse, intervalIntegral.integral_of_le ht, ← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => mul_smul _ _ _)

end KVApproximation.Approximation
