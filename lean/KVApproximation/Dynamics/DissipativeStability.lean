module

public import KVApproximation.Dynamics.TrajectoryBounds
public import KVApproximation.Dynamics.CaratheodoryHalfLine
public import KVApproximation.Dynamics.DrivenUniqueness
public import KVApproximation.Dynamics.IntegralCurveRegularity
public import KVApproximation.Analysis.EnergyTrapping

/-!
# Stability around a dissipative reference equation
-/

public section

open MeasureTheory Set Metric
open scoped InnerProductSpace NNReal

namespace KVApproximation.Dynamics

private theorem norm_lipschitz_pair_le
    {V Q : Type*} [NormedAddCommGroup V] [NormedAddCommGroup Q]
    {H : V × Q → Q} {K : ℝ≥0} (hH : LipschitzWith K H)
    {v : V} {q : Q} {R C : ℝ} (hv : ‖v‖ ≤ R) (hq : ‖q‖ ≤ C) :
    ‖H (v, q)‖ ≤ (K : ℝ) * max R C + ‖H (0, 0)‖ := by
  calc
    _ ≤ ‖H (v, q) - H (0, 0)‖ + ‖H (0, 0)‖ := norm_le_norm_sub_add _ _
    _ ≤ (K : ℝ) * max ‖v‖ ‖q‖ + ‖H (0, 0)‖ := by
      gcongr
      simpa only [dist_eq_norm, Prod.norm_def, Prod.mk_sub_mk, sub_zero] using
        hH.dist_le_mul (v, q) (0, 0)
    _ ≤ _ := by gcongr

/-- Proposition B.13, dissipative stability argument: approximation of
a reference field on a closed state tube produces a unique bounded
trajectory with the exact finite-time perturbation bound. -/
theorem dissipative_driven_stability
    {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    [CompleteSpace Q] [FiniteDimensional ℝ Q]
    (e : BoundedTrajectory V) (r : BoundedTrajectory Q)
    (F G : V × Q → Q) (hr : IsKineticSolution e F r)
    {rate δRef margin forcing : ℝ}
    (hRate : 0 < rate) (_hRef : 0 < δRef)
    (hrBound : ∀ t : ℝ, 0 ≤ t → ‖r.value t‖ ≤ δRef)
    (hMargin : 0 < margin) (hforcing : 0 < forcing)
    (hmargin : forcing ≤ rate * margin)
    (hdiss : ∀ (v : V) (q q' : Q),
      ⟪q - q', F (v, q) - F (v, q')⟫_ℝ ≤ -rate * ‖q - q'‖ ^ 2)
    (hG : LocallyLipschitz G)
    (happrox : ∀ (v : V) (q : Q), ‖v‖ ≤ e.velocityBound →
      ‖q‖ ≤ δRef + margin → ‖G (v, q) - F (v, q)‖ ≤ forcing) :
    ∃ q : BoundedTrajectory Q, IsKineticSolution e G q ∧
      (∀ q' : BoundedTrajectory Q, IsKineticSolution e G q' → q.Agree q') ∧
      (∀ t : ℝ, 0 ≤ t → ‖q.value t - r.value t‖ ≤
        forcing / rate * (1 - Real.exp (-rate * t))) := by
  classical
  let S := closedBall (0 : V) e.velocityBound ×ˢ closedBall (0 : Q) (δRef + margin)
  have hS : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS hG.locallyLipschitzOn
  obtain ⟨H, hH, hEq⟩ := hK.extend_finite_dimension
  let L : ℝ≥0 := lipschitzExtensionConstant Q * K
  have hLip (s : ℝ) : LipschitzWith L (fun q => H (e.velocity s, q)) := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
      hH.dist_le_mul (e.velocity s, q) (e.velocity s, q')
  have hvMeas (b : ℝ) : AEStronglyMeasurable e.velocity (volume.restrict (Icc 0 b)) :=
    (e.velocity_memLp.mono_measure
      (Measure.restrict_mono_set volume Icc_subset_Ici_self)).aestronglyMeasurable
  have hvBound (b : ℝ) : ∀ᵐ s ∂volume.restrict (Icc 0 b), ‖e.velocity s‖ ≤ e.velocityBound :=
    ae_restrict_of_ae_restrict_of_subset Icc_subset_Ici_self e.norm_velocity_ae_le
  have hInt (b : ℝ) (x : ℝ → Q) (hx : ContinuousOn x (Icc 0 b)) :
      IntegrableOn (fun s => H (e.velocity s, x s)) (Icc 0 b) :=
    integrableOn_lipschitz_driven_field hH (hvMeas b) (hvBound b) hx
  obtain ⟨x, hxc, hx₀, hxi⟩ := exists_integral_solution_Ici
    (Filter.Eventually.of_forall hLip : ∀ᵐ s ∂volume.restrict (Ici 0),
      LipschitzWith L (fun q => H (e.velocity s, q))) (fun b _ => hInt b) (0 : Q)
  have hxLocal (b : ℝ) (hb : 0 ≤ b) : AbsolutelyContinuousOnInterval x 0 b ∧
      ∀ᵐ s ∂volume.restrict (Icc 0 b), HasDerivAt x (H (e.velocity s, x s)) s := by
    have hc := hxc.mono (show Icc (0 : ℝ) b ⊆ Ici 0 from Icc_subset_Ici_self)
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    let B := (L : ℝ) * max e.velocityBound C + ‖H (0, 0)‖
    have hB : 0 ≤ B := add_nonneg
      (mul_nonneg L.coe_nonneg (ENNReal.toReal_nonneg.trans (le_max_left _ _))) (norm_nonneg _)
    apply integral_curve_regularity (K := B.toNNReal) hb
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr (hInt b x hc))
    · filter_upwards [hvBound b, ae_restrict_mem measurableSet_Icc] with s hs hsmem
      rw [Real.coe_toNNReal _ hB]
      exact norm_lipschitz_pair_le hH hs (hC s hsmem)
    · intro t ht
      rw [hx₀]
      exact hxi t ht.1
  have hrLocal (b : ℝ) (hb : 0 ≤ b) : AbsolutelyContinuousOnInterval r.value 0 b ∧
      ∀ᵐ s ∂volume.restrict (Icc 0 b), HasDerivAt r.value (r.velocity s) s := by
    apply integral_curve_regularity (K := r.velocityBound.toNNReal) hb
      (r.velocity_intervalIntegrable le_rfl hb)
    · simpa only [Real.coe_toNNReal r.velocityBound
        (show 0 ≤ r.velocityBound from ENNReal.toReal_nonneg)] using
        ae_restrict_of_ae_restrict_of_subset
          (show Icc (0 : ℝ) b ⊆ Ici 0 from Icc_subset_Ici_self) r.norm_velocity_ae_le
    · intro t ht
      exact r.integral_eq t ht.1
  have hError (t : ℝ) (ht : 0 ≤ t) :
      ‖x t - r.value t‖ ≤ forcing / rate * (1 - Real.exp (-rate * t)) ∧
      ‖x t - r.value t‖ < margin := by
    have hxT := hxLocal t ht
    have hrT := hrLocal t ht
    have hd : ∀ᵐ s ∂volume.restrict (Icc 0 t),
        HasDerivAt (fun s => x s - r.value s) (H (e.velocity s, x s) - r.velocity s) s := by
      filter_upwards [hxT.2, hrT.2] with s hs hs'
      exact hs.sub hs'
    have he : ∀ᵐ s ∂volume.restrict (Icc 0 t), ‖x s - r.value s‖ ≤ margin →
        ⟪x s - r.value s, H (e.velocity s, x s) - r.velocity s⟫_ℝ ≤
          forcing * ‖x s - r.value s‖ - rate * ‖x s - r.value s‖ ^ 2 := by
      filter_upwards [hvBound t, ae_restrict_of_ae_restrict_of_subset Icc_subset_Ici_self hr.2,
        ae_restrict_mem measurableSet_Icc] with s hs hrv hsmem
      intro hz
      have hxB : ‖x s‖ ≤ δRef + margin := by
        have := norm_le_norm_sub_add (x s) (r.value s)
        linarith [hrBound s hsmem.1]
      have hagree : G (e.velocity s, x s) = H (e.velocity s, x s) :=
        hEq ⟨by simpa only [mem_closedBall_iff_norm, sub_zero] using hs,
          by simpa only [mem_closedBall_iff_norm, sub_zero] using hxB⟩
      have happ : ‖H (e.velocity s, x s) - F (e.velocity s, x s)‖ ≤ forcing := by
        rw [← hagree]
        exact happrox _ _ hs hxB
      rw [hrv, show H (e.velocity s, x s) - F (e.velocity s, r.value s) =
        (H (e.velocity s, x s) - F (e.velocity s, x s)) +
          (F (e.velocity s, x s) - F (e.velocity s, r.value s)) by abel,
        inner_add_right]
      have hpert := (real_inner_le_norm (x s - r.value s)
        (H (e.velocity s, x s) - F (e.velocity s, x s))).trans
          (mul_le_mul_of_nonneg_left happ (norm_nonneg _))
      have hdis := hdiss (e.velocity s) (x s) (r.value s)
      nlinarith
    have hzero : x 0 - r.value 0 = 0 := by rw [hx₀, hr.1, sub_self]
    simpa only [sub_zero, Pi.sub_apply] using Analysis.ac_energy_trapping_bound (hxT.1.sub hrT.1) hzero
      hRate hforcing hMargin hmargin hd he (right_mem_Icc.mpr ht)
  have hxBound (t : ℝ) (ht : 0 ≤ t) : ‖x t‖ ≤ δRef + margin := by
    have := norm_le_norm_sub_add (x t) (r.value t)
    have := (hError t ht).2
    linarith [hrBound t ht]
  have hxMeas : AEStronglyMeasurable x timeMeasure :=
    hxc.aestronglyMeasurable measurableSet_Ici
  have huMeas : AEStronglyMeasurable (fun s => H (e.velocity s, x s)) timeMeasure :=
    hH.continuous.comp_aestronglyMeasurable (e.velocity_memLp.aestronglyMeasurable.prodMk hxMeas)
  let q : BoundedTrajectory Q := {
    value := x
    velocity := fun s => H (e.velocity s, x s)
    value_memLp := memLp_top_of_bound hxMeas (δRef + margin) (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hxBound t ht)
    velocity_memLp := memLp_top_of_bound huMeas
      ((L : ℝ) * max e.velocityBound (δRef + margin) + ‖H (0, 0)‖) (by
        filter_upwards [e.norm_velocity_ae_le, ae_restrict_mem measurableSet_Ici] with t ht ht'
        exact norm_lipschitz_pair_le hH ht (hxBound t ht'))
    integral_eq := by intro t ht; rw [hx₀]; exact hxi t ht
  }
  have hq : IsKineticSolution e G q := by
    refine ⟨hx₀, ?_⟩
    filter_upwards [e.norm_velocity_ae_le, ae_restrict_mem measurableSet_Ici] with t ht ht'
    exact (hEq ⟨by simpa only [mem_closedBall_iff_norm, sub_zero] using ht,
      by simpa only [mem_closedBall_iff_norm, sub_zero] using hxBound t ht'⟩).symm
  have hIntegral (z : BoundedTrajectory Q) (hz : IsKineticSolution e G z)
      (t : ℝ) (ht : 0 ≤ t) : z.value t = (0 : Q) + ∫ s in (0 : ℝ)..t, G (e.velocity s, z.value s) := by
    rw [z.integral_eq t ht, hz.1]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_imp_of_ae_restrict hz.2] with s hs hst
    rw [uIoc_of_le ht] at hst
    exact hs hst.1.le
  refine ⟨q, hq, ?_, fun t ht => (hError t ht).1⟩
  intro q' hq'
  have hValues (t : ℝ) (ht : 0 ≤ t) : q.value t = q'.value t :=
    locally_lipschitz_driven_unique_Icc hG (hvMeas t) (hvBound t)
      (q.continuousOn_value.mono Icc_subset_Ici_self)
      (q'.continuousOn_value.mono Icc_subset_Ici_self)
      (fun s hs => hIntegral q hq s hs.1) (fun s hs => hIntegral q' hq' s hs.1)
      (right_mem_Icc.mpr ht)
  refine ⟨hValues, ?_⟩
  filter_upwards [hq.2, hq'.2, ae_restrict_mem measurableSet_Ici] with t ht ht' htm
  rw [ht, ht', hValues t htm]

end KVApproximation.Dynamics
