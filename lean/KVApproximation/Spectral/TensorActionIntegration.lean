module

public import KVApproximation.Spectral.TensorActionIntegral
public import KVApproximation.Spectral.WeightedMeasureIntegration
public import KVApproximation.Tensor.LinearActionIdentities

/-!
# Vector-valued tests of the spectral tensor measure
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Tensor

namespace KVApproximation.Spectral

/-- Proposition B.10: a continuous vector test on the supported compact
spectral interval is integrable against the full Frobenius variation. -/
theorem TensorMeasure.integrable_continuousOn_vector {d : ℕ} {a b : ℝ}
    {F : Type*} [NormedAddCommGroup F] (ν : TensorMeasure d)
    (hfinite : totalVariation ν Set.univ < ⊤) (hsupport : ν.SupportedOn (Set.Icc a b))
    (f : ℝ → F) (hf : ContinuousOn f (Set.Icc a b)) : Integrable f ν.variation := by
  let : IsFiniteMeasure ν.variation := ⟨hfinite⟩
  have hrestrict : ν.variation.restrict (Set.Icc a b) = ν.variation :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport)
  have hi := hf.integrableOn_Icc (μ := ν.variation)
  rwa [IntegrableOn, hrestrict] at hi

/-- Proposition B.10, coefficient assembly: a fixed strain commutes with
the scalar test integral and the tensor action. -/
theorem tensorActionIntegral_smul {d : ℕ} (ν : TensorMeasure d)
    (f : ℝ → ℝ) (hf : Integrable f ν.variation) (e : Symmetric d) :
    tensorActionIntegral ν (fun r => f r • e) = action (tensorIntegral ν f) e := by
  let B := (actionL d).flip
  let S : ℝ →L[ℝ] Symmetric d := (ContinuousLinearMap.lsmul ℝ ℝ).flip e
  let D : Elasticity d →L[ℝ] Symmetric d := (actionL d).flip e
  have hB : B.comp S =
      (ContinuousLinearMap.compL ℝ (Elasticity d) (Elasticity d) (Symmetric d) D).comp
        (ContinuousLinearMap.lsmul ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro r
    apply ContinuousLinearMap.ext
    intro A
    change actionL d A (r • e) = actionL d (r • A) e
    simp only [map_smul, smul_apply]
  change VectorMeasure.integral ν (fun r => S (f r)) B =
    D (VectorMeasure.integral ν f (ContinuousLinearMap.lsmul ℝ ℝ))
  rw [VectorMeasure.integral_continuousLinearMap_comp hf, hB]
  exact (VectorMeasure.continuousLinearMap_apply_integral hf).symm

/-- Proposition B.10, error estimate: tensor contraction has norm at most
one, so integration costs only the Frobenius total variation. -/
theorem norm_tensorActionIntegral_le {d : ℕ} (ν : TensorMeasure d)
    (hfinite : totalVariation ν Set.univ < ⊤) (f : ℝ → Symmetric d)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ r ∂ν.variation, ‖f r‖ ≤ C) :
    ‖tensorActionIntegral ν f‖ ≤ C * (totalVariation ν Set.univ).toReal := by
  let : NormedAddCommGroup (Symmetric d) := (symmetricSubmodule d).normedAddCommGroup
  let : NormedSpace ℝ (Symmetric d) := (symmetricSubmodule d).normedSpace
  let : NormedAddCommGroup (Elasticity d) := (elasticitySubmodule d).normedAddCommGroup
  let : NormedSpace ℝ (Elasticity d) := (elasticitySubmodule d).normedSpace
  let : IsFiniteMeasure ν.variation := ⟨hfinite⟩
  have hB : ‖(actionL d).flip‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one
    intro e A
    change ‖action A e‖ ≤ 1 * ‖e‖ * ‖A‖
    simpa only [one_mul, mul_comm] using norm_action_le A e
  have hi := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := ν) (B := (actionL d).flip) hbound
  apply hi.trans
  change C * ‖(actionL d).flip‖ * (ν.variation Set.univ).toReal ≤
    C * (ν.variation Set.univ).toReal
  calc
    _ ≤ C * 1 * (ν.variation Set.univ).toReal := by gcongr
    _ = _ := by rw [mul_one]

private theorem tensorActionIntegral_eq_sum {d : ℕ} {ι : Type*} [Fintype ι]
    (ν : TensorMeasure d) (b : OrthonormalBasis ι ℝ (Symmetric d))
    (f : ℝ → Symmetric d) (hf : Integrable f ν.variation) :
    tensorActionIntegral ν f =
      ∑ k, action (tensorIntegral ν (fun r => ⟪b k, f r⟫_ℝ)) (b k) := by
  classical
  have hgi (k : ι) : Integrable (fun r => ⟪b k, f r⟫_ℝ) ν.variation :=
    (innerSL ℝ (b k)).integrable_comp hf
  calc
    tensorActionIntegral ν f =
        tensorActionIntegral ν (fun r => ∑ k, ⟪b k, f r⟫_ℝ • b k) := by
      congr 1
      funext r
      exact (b.sum_repr' (f r)).symm
    _ = ∑ k, tensorActionIntegral ν (fun r => ⟪b k, f r⟫_ℝ • b k) :=
      VectorMeasure.integral_finsetSum _ (fun k _ => (hgi k).smul_const (b k))
    _ = _ := Finset.sum_congr rfl (fun k _ => tensorActionIntegral_smul ν _ (hgi k) (b k))

/-- Proposition B.10, weighted memory representation: the resolvent
weight passes from the tensor measure to a continuous vector-valued test. -/
theorem weightedMeasure_actionIntegral {d : ℕ} {lower upper c : ℝ}
    (hlower : 0 < lower) (hc : 0 < c) (ν : TensorMeasure d)
    (hνpos : ν.Positive) (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (f : ℝ → Symmetric d) (hf : ContinuousOn f (Set.Icc lower upper)) :
    tensorActionIntegral (weightedMeasure c ν) f =
      tensorActionIntegral ν (fun r => resolventWeight c r • f r) := by
  obtain ⟨_, _, hsupport, hvar⟩ :=
    weightedMeasure_properties hlower hc ν hνpos hνsupport hνfinite
  have hμf := (weightedMeasure c ν).integrable_continuousOn_vector
    (hvar.trans_lt hνfinite) hsupport f hf
  have hwcont : ContinuousOn (resolventWeight c) (Set.Icc lower upper) :=
    continuousOn_id.div (continuousOn_const.add continuousOn_id)
      (fun r hr => (add_pos hc (hlower.trans_le hr.1)).ne')
  have hνwf := ν.integrable_continuousOn_vector hνfinite hνsupport _ (hwcont.smul hf)
  change Integrable (fun r => resolventWeight c r • f r) ν.variation at hνwf
  let b := stdOrthonormalBasis ℝ (Symmetric d)
  rw [tensorActionIntegral_eq_sum _ b _ hμf, tensorActionIntegral_eq_sum _ b _ hνwf]
  apply Finset.sum_congr rfl
  intro k _
  have htest : ContinuousOn (fun r => ⟪b k, f r⟫_ℝ) (Set.Icc lower upper) :=
    (innerSL ℝ (b k)).continuous.comp_continuousOn hf
  rw [(weightedMeasure_integral hlower hc ν hνpos hνsupport hνfinite _ htest).2]
  congr 2
  funext r
  simpa only [mul_comm] using
    (real_inner_smul_right (b k) (f r) (resolventWeight c r)).symm

end KVApproximation.Spectral
