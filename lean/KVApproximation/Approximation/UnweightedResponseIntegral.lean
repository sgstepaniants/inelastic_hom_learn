module

public import KVApproximation.Approximation.RealResponseIdentities
public import KVApproximation.Approximation.PartitionResponseContinuity
public import KVApproximation.Approximation.AlternativeProny
public import KVApproximation.Spectral.TensorActionIntegration
public import KVApproximation.Spectral.TensorActionFubini

/-!
# Exact integrals for the unweighted construction
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Remark 4.6: the unweighted response integral equals the cell memory convolution. -/
theorem memory_eq_unweightedResponseIntegral {d : ℕ} {lower upper : ℝ}
    (hlower : 0 < lower) (ν : TensorMeasure d) (K : ℝ → Elasticity d)
    (hrep : IsSpectralRepresentation ν K lower upper)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, action (K (t - s)) (e.velocity s)) =
      tensorActionIntegral ν (realWeightedResponse 0 e t) := by
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
  rw [intervalIntegral.integral_of_le ht]
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
      exact Filter.Eventually.of_forall (fun r => by
        rw [realWeightedResponse, zero_add, dampedResponse,
          intervalIntegral.integral_of_le ht, ← integral_smul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => mul_smul _ _ _))

/-- Remark 4.6: signed unweighted coefficients assemble the partitioned interpolant. -/
theorem unweighted_prony_stress_eq_partitionIntegral {M : Type*} {d : ℕ}
    (ν : M → TensorMeasure d) (Vhom Ehom : M → Elasticity d)
    {lower upper : ℝ} (hlower : 0 < lower) (m : ℕ) (a : M)
    (hνsupport : (ν a).SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation (ν a) Set.univ < ⊤)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (unweightedLocalModel ν Vhom Ehom lower upper m).stress a e t =
      action (Vhom a) (e.velocity t) + action (Ehom a) (e.value t) +
        tensorActionIntegral (ν a) (partitionResponse 0 lower upper m e t) := by
  let μ := ν a
  let R := logarithmicSpan lower upper
  let rate := localPronyRate lower upper m
  let coeff := unweightedLocalCoefficient (ν a) lower upper m
  let w (j : Fin (logPartitionCount R)) (i : Fin m) (r : ℝ) :=
    spectralWeight lower upper j r * (chebyshevLagrange m i).eval (localCoordinate lower R j r)
  let W (j : Fin (logPartitionCount R)) (i : Fin m) := realWeightedResponse 0 e t (rate j i)
  have hwi (j : Fin (logPartitionCount R)) (i : Fin m) : Integrable (w j i) μ.variation :=
    μ.integrable_continuousOn hνfinite hνsupport _
      (continuousOn_localPronyWeight hlower m j i)
  have hgi (j : Fin (logPartitionCount R)) (i : Fin m) :
      Integrable (fun r => w j i r • W j i) μ.variation := (hwi j i).smul_const (W j i)
  have hterm (j : Fin (logPartitionCount R)) (i : Fin m) :
      tensorActionIntegral μ (fun r => w j i r • W j i) =
        action (coeff j i) (dampedResponse (rate j i) e.velocity t) := by
    rw [tensorActionIntegral_smul μ _ (hwi j i)]
    change actionL d (tensorIntegral μ (w j i))
      ((0 + rate j i) • dampedResponse (rate j i) e.velocity t) =
      actionL d ((rate j i) • tensorIntegral μ (w j i))
        (dampedResponse (rate j i) e.velocity t)
    simp only [zero_add, map_smul, smul_apply]
  have hpartition : partitionResponse 0 lower upper m e t =
      fun r => ∑ j, ∑ i, w j i r • W j i := by
    funext r
    simp only [partitionResponse, realLocalResponseInterpolant, Finset.smul_sum, smul_smul]
    rfl
  have hint : tensorActionIntegral μ (partitionResponse 0 lower upper m e t) =
      ∑ j, ∑ i, action (coeff j i) (dampedResponse (rate j i) e.velocity t) := by
    rw [hpartition]
    calc
      _ = ∑ j, tensorActionIntegral μ (fun r => ∑ i, w j i r • W j i) :=
        VectorMeasure.integral_finsetSum _ (fun j _ =>
          integrable_finsetSum _ (fun i _ => hgi j i))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show tensorActionIntegral μ (fun r => ∑ i, w j i r • W j i) =
            ∑ i, tensorActionIntegral μ (fun r => w j i r • W j i) from
          VectorMeasure.integral_finsetSum _ (fun i _ => hgi j i)]
        exact Finset.sum_congr rfl (fun i _ => hterm j i)
  have hstate (j : Fin (logPartitionCount R)) (i : Fin m) :
      (∫ s in (0 : ℝ)..t, Real.exp (-rate j i * (t - s)) •
        actionL d (coeff j i) (e.velocity s)) =
      action (coeff j i) (dampedResponse (rate j i) e.velocity t) := by
    have hi : IntervalIntegrable
        (fun s => Real.exp (-rate j i * (t - s)) • e.velocity s) volume 0 t :=
      (e.velocity_intervalIntegrable le_rfl ht).continuousOn_smul (by fun_prop)
    simpa only [map_smul, actionL_apply, dampedResponse] using
      (actionL d (coeff j i)).intervalIntegral_comp_comm hi
  rw [hint]
  unfold PronyModel.stress PronyModel.stressResponse PronyModel.state unweightedLocalModel
  congr 1
  change (∑ k, ∫ s in (0 : ℝ)..t,
    Real.exp (-rate (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 * (t - s)) •
      actionL d (coeff (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) (e.velocity s)) = _
  rw [Fintype.sum_equiv finProdFinEquiv.symm _
    (fun ji => ∫ s in (0 : ℝ)..t, Real.exp (-rate ji.1 ji.2 * (t - s)) •
      actionL d (coeff ji.1 ji.2) (e.velocity s)) (fun _ => rfl), Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hstate j i))


end KVApproximation.Approximation
