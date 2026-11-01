module

public import KVApproximation.NeuralOperators.StateCoordinates
public import KVApproximation.Dynamics.DissipativeStability
public import KVApproximation.Dynamics.PronyDissipation
public import KVApproximation.Dynamics.PronyTrajectory
public import KVApproximation.Dynamics.PronyMeasurability
public import KVApproximation.Dynamics.TrajectoryMaps

/-!
# Uniform Prony response bounds in isometric state coordinates
-/

public section

open MeasureTheory KVApproximation.Dynamics
open scoped InnerProductSpace

namespace KVApproximation.NeuralOperators

/-- Proposition B.13 (`eq:ua_err`): at every material and admissible
strain, the same response tolerances give the unique scalar-coordinate
trajectory and the two full-half-line essential-supremum error bounds. -/
theorem prony_response_stability
    {M E Q : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    [CompleteSpace Q] [FiniteDimensional ℝ Q]
    {n : ℕ} (P : PronyModel M E n) (a : M) (T : BlockState n E ≃ₗᵢ[ℝ] Q)
    (e : BoundedTrajectory E) {βE βV δ rateLower δIV η εF εG : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hRateLower : 0 < rateLower) (hRate : ∀ k, rateLower ≤ P.rate k)
    (hδIV : 0 < δIV) (hIV : ∀ t : ℝ, 0 ≤ t → ‖P.state a e t‖ ≤ δIV)
    (hη : 0 < η) (_hεF : 0 < εF) (hεG : 0 < εG) (hmargin : εG ≤ rateLower * η)
    (F : C(StressInput E Q, E)) (G : C(KineticInput E Q, Q)) (hG : LocallyLipschitz G)
    (hFapprox : ∀ x ∈ stressInputSet βE βV δ (δIV + η),
      ‖F x - coordinateStressResponse P T a x‖ ≤ εF)
    (hGapprox : ∀ x ∈ kineticInputSet βV δ (δIV + η),
      ‖G x - coordinateKineticResponse P T a x‖ ≤ εG) :
    ∃ q : BoundedTrajectory Q,
      IsKineticSolution e (fun vq => G (WithLp.toLp 2 vq)) q ∧
      (∀ q' : BoundedTrajectory Q,
        IsKineticSolution e (fun vq => G (WithLp.toLp 2 vq)) q' → q.Agree q') ∧
      (∀ t : ℝ, 0 ≤ t → ‖q.value t - T (P.state a e t)‖ ≤
        εG / rateLower * (1 - Real.exp (-rateLower * t))) ∧
      eLpNorm (fun t => q.value t - T (P.state a e t)) ⊤ timeMeasure ≤
        ENNReal.ofReal (εG / rateLower) ∧
      eLpNorm (fun t => F (WithLp.toLp 2
        (e.value t, WithLp.toLp 2 (e.velocity t, q.value t))) - P.stress a e t)
        ⊤ timeMeasure ≤ ENNReal.ofReal (εF + Real.sqrt n * εG / rateLower) := by
  obtain ⟨r₀, hrValue, hr₀⟩ := pronyState_isKineticSolution P
    (fun k => hRateLower.trans_le (hRate k)) a e
  let r := r₀.map T.toContinuousLinearEquiv.toContinuousLinearMap
  let GIV : E × Q → Q := fun vq => T (P.kineticResponse a vq.1 (T.symm vq.2))
  let GNO : E × Q → Q := fun vq => G (WithLp.toLp 2 vq)
  have hr : IsKineticSolution e GIV r := by
    refine ⟨?_, ?_⟩
    · change T (r₀.value 0) = 0
      rw [hr₀.1, map_zero]
    · filter_upwards [hr₀.2] with t ht
      change T (r₀.velocity t) = T (P.kineticResponse a (e.velocity t) (T.symm (T (r₀.value t))))
      rw [T.symm_apply_apply, ht]
  have hrV (t : ℝ) (ht : 0 ≤ t) : r.value t = T (P.state a e t) := by
    change T (r₀.value t) = _
    rw [hrValue t ht]
  have hvel : βV * e.velocityBound ≤ δ := by
    have hnonneg : 0 ≤ βE * e.valueBound := mul_nonneg hβE.le ENNReal.toReal_nonneg
    change βE * e.valueBound + βV * e.velocityBound ≤ δ at he
    linarith
  have hGLip : LocallyLipschitz GNO :=
    hG.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E Q).symm.toContinuousLinearMap.lipschitzWith.locallyLipschitz
  have hdis (v : E) (q q' : Q) :
      ⟪q - q', GIV (v, q) - GIV (v, q')⟫_ℝ ≤ -rateLower * ‖q - q'‖ ^ 2 := by
    change ⟪q - q', T (P.kineticResponse a v (T.symm q)) -
      T (P.kineticResponse a v (T.symm q'))⟫_ℝ ≤ _
    rw [← T.symm.inner_map_map, map_sub, map_sub, T.symm_apply_apply, T.symm_apply_apply]
    have hd := prony_kinetic_dissipative P a hRate v (T.symm q) (T.symm q')
    have hn : ‖T.symm q - T.symm q'‖ = ‖q - q'‖ := by rw [← map_sub, T.symm.norm_map]
    simpa only [hn] using hd
  obtain ⟨q, hq, hUnique, hError⟩ := dissipative_driven_stability e r GIV GNO hr
    hRateLower hδIV (fun t ht => by rw [hrV t ht, T.norm_map]; exact hIV t ht)
    hη hεG hmargin hdis hGLip (by
      intro v q hv hq
      have hb := hGapprox (WithLp.toLp 2 (v, q))
        ⟨(mul_le_mul_of_nonneg_left hv hβV.le).trans hvel, hq⟩
      exact hb)
  have hFinite (t : ℝ) (ht : 0 ≤ t) : ‖q.value t - T (P.state a e t)‖ ≤
      εG / rateLower * (1 - Real.exp (-rateLower * t)) := by
    simpa only [hrV t ht] using hError t ht
  have hPoint (t : ℝ) (ht : 0 ≤ t) : ‖q.value t - T (P.state a e t)‖ ≤ εG / rateLower := by
    have hpos := div_pos hεG hRateLower
    have hexp := Real.exp_pos (-rateLower * t)
    have hnonneg := mul_nonneg hpos.le hexp.le
    nlinarith [hFinite t ht]
  have hTube (t : ℝ) (ht : 0 ≤ t) : ‖q.value t‖ ≤ δIV + η := by
    have hn := norm_le_norm_sub_add (q.value t) (T (P.state a e t))
    have hmargin' : εG / rateLower ≤ η :=
      (div_le_iff₀ hRateLower).mpr (by simpa only [mul_comm] using hmargin)
    rw [T.norm_map] at hn
    linarith [hPoint t ht, hIV t ht]
  have hrMeas : AEStronglyMeasurable (fun t => T (P.state a e t)) timeMeasure := by
    apply r.value_memLp.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hrV t ht
  have hInput : AEStronglyMeasurable (fun t => WithLp.toLp 2
      (e.value t, WithLp.toLp 2 (e.velocity t, q.value t))) timeMeasure :=
    (WithLp.prod_continuous_toLp 2 E (WithLp 2 (E × Q))).comp_aestronglyMeasurable
      (e.value_memLp.aestronglyMeasurable.prodMk
        ((WithLp.prod_continuous_toLp 2 E Q).comp_aestronglyMeasurable
          (e.velocity_memLp.aestronglyMeasurable.prodMk q.value_memLp.aestronglyMeasurable)))
  refine ⟨q, hq, hUnique, hFinite, ?_, ?_⟩
  · have hdiff : AEStronglyMeasurable (fun t => q.value t - T (P.state a e t)) timeMeasure :=
      q.value_memLp.aestronglyMeasurable.sub hrMeas
    rw [eLpNorm_exponent_top hdiff]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hPoint t ht
  · have hdiff : AEStronglyMeasurable (fun t => F (WithLp.toLp 2
        (e.value t, WithLp.toLp 2 (e.velocity t, q.value t))) - P.stress a e t) timeMeasure :=
      (F.continuous.comp_aestronglyMeasurable hInput).sub (aestronglyMeasurable_pronyStress P a e)
    rw [eLpNorm_exponent_top hdiff]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [e.norm_velocity_ae_le, ae_restrict_mem measurableSet_Ici] with t ht ht'
    have hbudget : βE * ‖e.value t‖ + βV * ‖e.velocity t‖ ≤ δ :=
      (add_le_add (mul_le_mul_of_nonneg_left (e.norm_value_le ht') hβE.le)
        (mul_le_mul_of_nonneg_left ht hβV.le)).trans he
    have hF' := hFapprox (WithLp.toLp 2
      (e.value t, WithLp.toLp 2 (e.velocity t, q.value t))) ⟨hbudget, hTube t ht'⟩
    have hState : ‖T.symm (q.value t) - P.state a e t‖ ≤ εG / rateLower := by
      rw [← T.norm_map (T.symm (q.value t) - P.state a e t), map_sub, T.apply_symm_apply]
      exact hPoint t ht'
    exact stress_error_le P a hF' hState

end KVApproximation.NeuralOperators
