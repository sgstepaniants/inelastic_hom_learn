import KVApproximation.Approximation.UnweightedResponseBound
import KVApproximation.Approximation.LocalRateGeometry
import KVApproximation.Approximation.ChebyshevInterpolation
import KVApproximation.Approximation.RealResponseIdentities
import KVApproximation.Approximation.PartitionResponseContinuity
import KVApproximation.Spectral.TensorActionIntegration

/-!
# Local interpolation without resolvent reweighting
-/

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

-- Keep the scalar structures identical to the independent statements.
attribute [local instance 2000] NormedField.toNormedCommRing
attribute [local instance 3000] Real.normedCommRing

/-- Remark 4.6, local Chebyshev estimate without resolvent reweighting. -/
theorem local_unweighted_response_error {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (J : E →ₗᵢ[ℝ] F) (e : BoundedTrajectory E) {βE βV δ lower R t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 0 < R) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) (j : Fin (logPartitionCount R))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖localWeightedResponse J.toContinuousLinearMap 0 lower R j e t x -
      chebyshevInterpolant m (localWeightedResponse J.toContinuousLinearMap 0 lower R j e t) x‖ ≤
      (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1) := by
  let M := δ / (βV * Real.cos (3 / 4))
  have hvalue : 0 ≤ βE * e.valueBound := mul_nonneg hβE.le ENNReal.toReal_nonneg
  have hvel : e.velocityBound ≤ δ / βV := by
    apply (le_div_iff₀ hβV).mpr
    change βE * e.valueBound + βV * e.velocityBound ≤ δ at he
    nlinarith
  have hδ : 0 ≤ δ := (add_nonneg hvalue (mul_nonneg hβV.le ENNReal.toReal_nonneg)).trans he
  have hcos : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
  have hM : 0 ≤ M := div_nonneg hδ (mul_pos hβV hcos).le
  have hrate (z : ℂ) : AnalyticAt ℂ (complexLocalRate lower R j) z := by
    unfold complexLocalRate
    fun_prop
  have hweighted := weightedResponse_entire J.toContinuousLinearMap 0 e ht
  have hanalytic : AnalyticOnNhd ℂ (localWeightedResponse J.toContinuousLinearMap 0 lower R j e t)
      (bernsteinEllipse 2) := by
    intro z _
    exact (hweighted (complexLocalRate lower R j z) (Set.mem_univ _)).comp (hrate z)
  have hbound (z : ℂ) (hz : z ∈ bernsteinEllipse 2) :
      ‖localWeightedResponse J.toContinuousLinearMap 0 lower R j e t z‖ ≤ M := by
    have hgeom := complexLocalRate_ellipse hlower hR j hz
    calc
      _ ≤ ‖complexLocalRate lower R j z‖ / (complexLocalRate lower R j z).re * e.velocityBound :=
        norm_unweightedResponse_le J e ht hgeom.1
      _ ≤ (Real.cos (3 / 4))⁻¹ * (δ / βV) :=
        mul_le_mul hgeom.2 hvel ENNReal.toReal_nonneg (inv_nonneg.mpr hcos.le)
      _ = M := by dsimp [M]; ring
  calc
    _ ≤ chebyshevErrorBound M 2 m :=
      chebyshevInterpolant_error_le (by norm_num) hM (lt_of_lt_of_le Nat.zero_lt_one hm)
        hanalytic hbound x hx
    _ = _ := by simp only [chebyshevErrorBound, M]; norm_num; ring

/-- Remark 4.6: real coordinates preserve the local unweighted error. -/
theorem real_local_unweighted_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower R t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 0 < R) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) (j : Fin (logPartitionCount R))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖realWeightedResponse 0 e t (localRate lower R j x) -
      realLocalResponseInterpolant 0 lower R m j e t x‖ ≤
      (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1) := by
  let J := TauCeti.Complexification.ofRealLI E
  have hmap (y : ℝ) : J (realWeightedResponse 0 e t (localRate lower R j y)) =
      localWeightedResponse J.toContinuousLinearMap 0 lower R j e t y := by
    rw [localWeightedResponse, complexLocalRate_ofReal]
    exact map_realWeightedResponse J.toContinuousLinearMap _ e ht _
  have hpoly : J (realLocalResponseInterpolant 0 lower R m j e t x) =
      chebyshevInterpolant m (localWeightedResponse J.toContinuousLinearMap 0 lower R j e t) x := by
    simp only [realLocalResponseInterpolant, chebyshevInterpolant, map_sum, map_smul,
      hmap, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have h := local_unweighted_response_error J e hβE hβV he hlower hR ht hm j hx
  rw [← hmap x, ← hpoly, ← J.map_sub, J.norm_map] at h
  exact h

/-- Remark 4.6: nonnegative patch weights preserve the unweighted error constant. -/
theorem partition_unweighted_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower upper t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) {r : ℝ} (hr : r ∈ Set.Icc lower upper) :
    ‖realWeightedResponse 0 e t r - partitionResponse 0 lower upper m e t r‖ ≤
      (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1) := by
  let R := logarithmicSpan lower upper
  let w := spectralWeight lower upper
  let W := realWeightedResponse 0 e t r
  let p (j : Fin (logPartitionCount R)) :=
    realLocalResponseInterpolant 0 lower R m j e t (localCoordinate lower R j r)
  let B := (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1)
  have hR : 0 < R := logarithmicSpan_pos hlower horder
  have hsum : ∑ j, w j r = 1 := sum_spectralWeight hlower horder hr
  have heq : W - partitionResponse 0 lower upper m e t r = ∑ j, w j r • (W - p j) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
    rfl
  have hlocal (j : Fin (logPartitionCount R)) : ‖w j r • (W - p j)‖ ≤ w j r * B := by
    by_cases hp : r ∈ Set.Icc (lower * Real.exp (logPatchLeft R j))
        (lower * Real.exp (logPatchRight R j))
    · have h := real_local_unweighted_response_error e hβE hβV he hlower hR ht hm j
        (localCoordinate_mem hlower hR j hp)
      rw [localRate_localCoordinate hlower hR j (hlower.trans_le hr.1)] at h
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (spectralWeight_nonneg _ _ j r)]
      exact mul_le_mul_of_nonneg_left h (spectralWeight_nonneg _ _ j r)
    · have hz : w j r = 0 := spectralWeight_eq_zero_of_not_mem hlower horder j hr hp
      simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
  change ‖W - partitionResponse 0 lower upper m e t r‖ ≤ B
  rw [heq]
  calc
    _ ≤ ∑ j, ‖w j r • (W - p j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, w j r * B := Finset.sum_le_sum (fun j _ => hlocal j)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Remark 4.6: integration costs the unweighted spectral measure's total variation. -/
theorem norm_integrated_unweighted_partition_error_le {d : ℕ}
    (ν : TensorMeasure d) {βE βV δ lower upper t : ℝ}
    (hνfinite : totalVariation ν Set.univ < ⊤)
    (hνsupport : ν.SupportedOn (Set.Icc lower upper))
    (e : BoundedTrajectory (Symmetric d))
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (horder : lower < upper) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖tensorActionIntegral ν (realWeightedResponse 0 e t) -
      tensorActionIntegral ν (partitionResponse 0 lower upper m e t)‖ ≤
      ((4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1)) *
        (totalVariation ν Set.univ).toReal := by
  have hW := ν.integrable_continuousOn_vector hνfinite hνsupport _
    (continuous_realWeightedResponse 0 e ht).continuousOn
  have hp := ν.integrable_continuousOn_vector hνfinite hνsupport _
    (continuousOn_partitionResponse 0 hlower m e t)
  have hnonneg : 0 ≤ (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1) :=
    (norm_nonneg _).trans (partition_unweighted_response_error e hβE hβV he hlower horder ht hm
      (show lower ∈ Set.Icc lower upper from ⟨le_rfl, horder.le⟩))
  rw [tensorActionIntegral, tensorActionIntegral, ← VectorMeasure.integral_sub hW hp]
  apply norm_tensorActionIntegral_le ν hνfinite _ hnonneg
  filter_upwards [ae_iff.mpr hνsupport] with r hr
  exact partition_unweighted_response_error e hβE hβV he hlower horder ht hm hr

end KVApproximation.Approximation
