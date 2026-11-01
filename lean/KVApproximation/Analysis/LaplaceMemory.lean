module

public import KVApproximation.Analysis.HalfLineConvolution
public import KVApproximation.Analysis.HalfLineLaplaceDamping
public import KVApproximation.Analysis.HalfLineLaplacePrimitive

/-!
# Integrated memory equations from Laplace transforms

The integrated residual is continuous and becomes bounded after exponential
damping. Its transform is the prepared elliptic balance divided by the rate.
-/

public section

open MeasureTheory Set

namespace KVApproximation.Analysis

/-- Theorem 3.1, integrated residual: the primitive of a continuous
half-line trajectory is continuous up to its initial time. -/
private theorem continuousOn_primitive_Ici {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : ℝ → H) (hu : ContinuousOn u (Ici (0 : ℝ))) :
    ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, u r) (Ici (0 : ℝ)) := by
  have hc := continuousOn_posConvolution_Ici
    (ContinuousLinearMap.lsmul ℝ ℝ) (fun _ => (1 : ℝ)) u continuous_const
    (fun T hT => (hu.mono (fun _ hr => hr.1)).intervalIntegrable_of_Icc hT)
  apply hc.congr
  intro t ht
  rw [posConvolution_eq_integral_sub _ _ _ ht]
  simp only [ContinuousLinearMap.lsmul_apply, one_smul]

/-- Theorem 3.1, integrated residual: a bounded trajectory has a
bounded exponentially damped primitive, with the same norm bound. -/
private theorem norm_exp_smul_primitive_le {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : ℝ → H) {M : ℝ} (hbound : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖Real.exp (-t) • (∫ r in (0 : ℝ)..t, u r)‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hbound 0 le_rfl)
  have hp : ‖∫ r in (0 : ℝ)..t, u r‖ ≤ M * t := by
    simpa only [sub_zero, abs_of_nonneg ht] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := t) (f := u) (fun r hr => hbound r (by
          rw [uIoc_of_le ht] at hr
          exact hr.1.le)))
  have he : t * Real.exp (-t) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one t).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (-t) * (M * t) := mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = M * (t * Real.exp (-t)) := by ring
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left he hM
    _ = M := mul_one M

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), time-domain
recovery: the prepared transformed equation determines the integrated memory
balance at every nonnegative time. -/
theorem integrated_memory_eq_zero_of_halfLineLaplace
    {H F G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K)
    (hKi : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t => Real.exp (-s * t) • K t) (Set.Ioi (0 : ℝ)))
    (u : ℝ → H) (hu : ContinuousOn u (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ M) (u₀ : H)
    (hLap : ∀ s : ℝ, 0 < s →
      (V + s⁻¹ • E + L (halfLineLaplace K s))
        (s • halfLineLaplace u s - u₀) = -s⁻¹ • E u₀) :
    ∀ t : ℝ, 0 ≤ t →
      V (u t - u₀) + E (∫ r in (0 : ℝ)..t, u r) +
        posConvolution K (fun r => u r - u₀) L volume t = 0 := by
  let q : ℝ → H := fun t => u t - u₀
  let p : ℝ → H := fun t => ∫ r in (0 : ℝ)..t, u r
  let J : ℝ → G := fun t => V (q t) + E (p t) + posConvolution K q L volume t
  have hq : ContinuousOn q (Ici (0 : ℝ)) := hu.sub continuousOn_const
  have hp : ContinuousOn p (Ici (0 : ℝ)) := continuousOn_primitive_Ici u hu
  have hqb (t : ℝ) (ht : 0 ≤ t) : ‖q t‖ ≤ M + ‖u₀‖ :=
    (norm_sub_le _ _).trans (add_le_add (hbound t ht) le_rfl)
  have hqLocal (T : ℝ) (hT : 0 ≤ T) : IntervalIntegrable q volume 0 T :=
    (hq.mono (fun _ hr => hr.1)).intervalIntegrable_of_Icc hT
  have hJ : ContinuousOn J (Ici (0 : ℝ)) :=
    ((V.continuous.comp_continuousOn hq).add (E.continuous.comp_continuousOn hp)).add
      (continuousOn_posConvolution_Ici L K q hK hqLocal)
  have hb (t : ℝ) (ht : 0 ≤ t) :
      ‖Real.exp (-(1 : ℝ) * t) • J t‖ ≤
        ‖V‖ * (M + ‖u₀‖) + ‖E‖ * M +
          ‖L‖ * (M + ‖u₀‖) * (∫ r in Ioi (0 : ℝ), ‖Real.exp (-r) • K r‖) := by
    have hqd : ‖Real.exp (-t) • q t‖ ≤ M + ‖u₀‖ := by
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ 1 * (M + ‖u₀‖) := mul_le_mul
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) (hqb t ht)
          (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hV : ‖Real.exp (-t) • V (q t)‖ ≤ ‖V‖ * (M + ‖u₀‖) := by
      rw [← map_smul]
      exact (V.le_opNorm _).trans (mul_le_mul_of_nonneg_left hqd (norm_nonneg V))
    have hE : ‖Real.exp (-t) • E (p t)‖ ≤ ‖E‖ * M := by
      rw [← map_smul]
      exact (E.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (norm_exp_smul_primitive_le u hbound ht) (norm_nonneg E))
    have hC : ‖Real.exp (-t) • posConvolution K q L volume t‖ ≤
        ‖L‖ * (M + ‖u₀‖) * (∫ r in Ioi (0 : ℝ), ‖Real.exp (-r) • K r‖) := by
      simpa only [neg_one_mul] using norm_exp_smul_posConvolution_le L K q hK hq
        hqb (a := 1) zero_le_one (hKi 1 zero_lt_one) ht
    simp only [J, neg_one_mul, smul_add]
    calc
      _ ≤ ‖Real.exp (-t) • V (q t) + Real.exp (-t) • E (p t)‖ +
          ‖Real.exp (-t) • posConvolution K q L volume t‖ := norm_add_le _ _
      _ ≤ (‖Real.exp (-t) • V (q t)‖ + ‖Real.exp (-t) • E (p t)‖) +
          ‖Real.exp (-t) • posConvolution K q L volume t‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add hV hE) hC
  have hJL (s : ℝ) (hs : 0 < s) : halfLineLaplace J s = 0 := by
    have hiu := integrable_halfLineLaplace u hu hbound hs
    have hiq := integrable_halfLineLaplace q hq hqb hs
    have hip := integrable_halfLineLaplace_primitive u hs hiu
    have hiV : IntegrableOn (fun t => V (Real.exp (-s * t) • q t)) (Ioi (0 : ℝ)) :=
      V.integrable_comp hiq
    have hiE : IntegrableOn (fun t => E (Real.exp (-s * t) • p t)) (Ioi (0 : ℝ)) :=
      E.integrable_comp hip
    have hiVE : IntegrableOn (fun t =>
        V (Real.exp (-s * t) • q t) + E (Real.exp (-s * t) • p t)) (Ioi (0 : ℝ)) :=
      hiV.add hiE
    have hiC := integrable_halfLineLaplace_posConvolution L K q s (hKi s hs) hiq
    have hqLap : halfLineLaplace q s = halfLineLaplace u s - s⁻¹ • u₀ := by
      change (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • (u t - u₀)) = _
      simp_rw [smul_sub]
      rw [integral_sub hiu (integrable_halfLineLaplace_const u₀ hs)]
      exact congrArg (fun z => halfLineLaplace u s - z) (halfLineLaplace_const u₀ hs)
    have hformula : halfLineLaplace J s =
        V (halfLineLaplace q s) + E (s⁻¹ • halfLineLaplace u s) +
          L (halfLineLaplace K s) (halfLineLaplace q s) := by
      calc
        halfLineLaplace J s = (∫ t in Ioi (0 : ℝ),
            (V (Real.exp (-s * t) • q t) + E (Real.exp (-s * t) • p t)) +
              Real.exp (-s * t) • posConvolution K q L volume t) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t => by
            simp only [J, smul_add, map_smul]
        _ = V (halfLineLaplace q s) + E (halfLineLaplace p s) +
            halfLineLaplace (posConvolution K q L volume) s := by
          rw [integral_add hiVE hiC, integral_add hiV hiE,
            V.integral_comp_comm hiq, E.integral_comp_comm hip]
          rfl
        _ = _ := by
          rw [show halfLineLaplace p s = s⁻¹ • halfLineLaplace u s from
            halfLineLaplace_primitive u hs hiu,
            halfLineLaplace_posConvolution L K q s (hKi s hs) hiq]
    have hscale : s • halfLineLaplace J s =
        (V + s⁻¹ • E + L (halfLineLaplace K s))
          (s • halfLineLaplace u s - u₀) + s⁻¹ • E u₀ := by
      rw [hformula, hqLap]
      simp only [add_apply, smul_apply, map_sub, map_smul, smul_add, smul_sub,
        smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
      abel
    have hz : s • halfLineLaplace J s = 0 := by
      rw [hscale, hLap s hs, neg_smul, neg_add_cancel]
    exact (smul_eq_zero.mp hz).resolve_left hs.ne'
  exact eq_zero_of_halfLineLaplace_eq_zero_of_damped_bound J hJ 1 hb
    (fun s hs => hJL s (lt_trans zero_lt_one hs))

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), viscously prepared
Green evolution: the transformed elliptic load gives a constant-load
integrated memory balance, including the viscous initial identity at zero. -/
theorem integrated_memory_eq_const_of_halfLineLaplace
    {H F G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K)
    (hKi : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t => Real.exp (-s * t) • K t) (Set.Ioi (0 : ℝ)))
    (u : ℝ → H) (hu : ContinuousOn u (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ M) (g : G)
    (hLap : ∀ s : ℝ, 0 < s →
      (V + s⁻¹ • E + L (halfLineLaplace K s)) (halfLineLaplace u s) = s⁻¹ • g) :
    ∀ t : ℝ, 0 ≤ t →
      V (u t) + E (∫ r in (0 : ℝ)..t, u r) + posConvolution K u L volume t = g := by
  let p : ℝ → H := fun t => ∫ r in (0 : ℝ)..t, u r
  let J : ℝ → G := fun t => V (u t) + E (p t) + posConvolution K u L volume t
  have hp : ContinuousOn p (Ici (0 : ℝ)) := continuousOn_primitive_Ici u hu
  have huLocal (T : ℝ) (hT : 0 ≤ T) : IntervalIntegrable u volume 0 T :=
    (hu.mono (fun _ hr => hr.1)).intervalIntegrable_of_Icc hT
  have hJ : ContinuousOn J (Ici (0 : ℝ)) :=
    ((V.continuous.comp_continuousOn hu).add (E.continuous.comp_continuousOn hp)).add
      (continuousOn_posConvolution_Ici L K u hK huLocal)
  have hb (t : ℝ) (ht : 0 ≤ t) :
      ‖Real.exp (-(1 : ℝ) * t) • (J t - g)‖ ≤
        ‖V‖ * M + ‖E‖ * M +
          ‖L‖ * M * (∫ r in Ioi (0 : ℝ), ‖Real.exp (-r) • K r‖) + ‖g‖ := by
    have hud : ‖Real.exp (-t) • u t‖ ≤ M := by
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ 1 * M := mul_le_mul
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) (hbound t ht)
          (norm_nonneg _) zero_le_one
        _ = M := one_mul M
    have hV : ‖Real.exp (-t) • V (u t)‖ ≤ ‖V‖ * M := by
      rw [← map_smul]
      exact (V.le_opNorm _).trans (mul_le_mul_of_nonneg_left hud (norm_nonneg V))
    have hE : ‖Real.exp (-t) • E (p t)‖ ≤ ‖E‖ * M := by
      rw [← map_smul]
      exact (E.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (norm_exp_smul_primitive_le u hbound ht) (norm_nonneg E))
    have hC : ‖Real.exp (-t) • posConvolution K u L volume t‖ ≤
        ‖L‖ * M * (∫ r in Ioi (0 : ℝ), ‖Real.exp (-r) • K r‖) := by
      simpa only [neg_one_mul] using norm_exp_smul_posConvolution_le L K u hK hu
        hbound (a := 1) zero_le_one (hKi 1 zero_lt_one) ht
    have hg : ‖Real.exp (-t) • g‖ ≤ ‖g‖ := by
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) (norm_nonneg g)
        _ = ‖g‖ := one_mul _
    simp only [neg_one_mul, smul_sub, J, smul_add]
    calc
      _ ≤ ‖Real.exp (-t) • V (u t) + Real.exp (-t) • E (p t) +
          Real.exp (-t) • posConvolution K u L volume t‖ + ‖Real.exp (-t) • g‖ :=
        norm_sub_le _ _
      _ ≤ (‖Real.exp (-t) • V (u t) + Real.exp (-t) • E (p t)‖ +
          ‖Real.exp (-t) • posConvolution K u L volume t‖) + ‖Real.exp (-t) • g‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖Real.exp (-t) • V (u t)‖ + ‖Real.exp (-t) • E (p t)‖) +
          ‖Real.exp (-t) • posConvolution K u L volume t‖) + ‖Real.exp (-t) • g‖ :=
        add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ ≤ _ := add_le_add (add_le_add (add_le_add hV hE) hC) hg
  have hRL (s : ℝ) (hs : 0 < s) : halfLineLaplace (fun t => J t - g) s = 0 := by
    have hiu := integrable_halfLineLaplace u hu hbound hs
    have hip := integrable_halfLineLaplace_primitive u hs hiu
    have hiV : IntegrableOn (fun t => V (Real.exp (-s * t) • u t)) (Ioi (0 : ℝ)) :=
      V.integrable_comp hiu
    have hiE : IntegrableOn (fun t => E (Real.exp (-s * t) • p t)) (Ioi (0 : ℝ)) :=
      E.integrable_comp hip
    have hiVE : IntegrableOn (fun t =>
        V (Real.exp (-s * t) • u t) + E (Real.exp (-s * t) • p t)) (Ioi (0 : ℝ)) :=
      hiV.add hiE
    have hiC := integrable_halfLineLaplace_posConvolution L K u s (hKi s hs) hiu
    have hiJ : IntegrableOn (fun t => Real.exp (-s * t) • J t) (Ioi (0 : ℝ)) := by
      have hiTotal : IntegrableOn (fun t =>
          V (Real.exp (-s * t) • u t) + E (Real.exp (-s * t) • p t) +
            Real.exp (-s * t) • posConvolution K u L volume t) (Ioi (0 : ℝ)) :=
        hiVE.add hiC
      simpa only [J, smul_add, map_smul] using hiTotal
    have hJL : halfLineLaplace J s = s⁻¹ • g := by
      calc
        halfLineLaplace J s = (∫ t in Ioi (0 : ℝ),
            (V (Real.exp (-s * t) • u t) + E (Real.exp (-s * t) • p t)) +
              Real.exp (-s * t) • posConvolution K u L volume t) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t => by
            simp only [J, smul_add, map_smul]
        _ = V (halfLineLaplace u s) + E (halfLineLaplace p s) +
            halfLineLaplace (posConvolution K u L volume) s := by
          rw [integral_add hiVE hiC, integral_add hiV hiE,
            V.integral_comp_comm hiu, E.integral_comp_comm hip]
          rfl
        _ = (V + s⁻¹ • E + L (halfLineLaplace K s)) (halfLineLaplace u s) := by
          rw [show halfLineLaplace p s = s⁻¹ • halfLineLaplace u s from
            halfLineLaplace_primitive u hs hiu,
            halfLineLaplace_posConvolution L K u s (hKi s hs) hiu]
          simp only [add_apply, smul_apply, map_smul]
        _ = s⁻¹ • g := hLap s hs
    change (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • (J t - g)) = 0
    simp_rw [smul_sub]
    rw [integral_sub hiJ (integrable_halfLineLaplace_const g hs)]
    change halfLineLaplace J s - halfLineLaplace (fun _ => g) s = 0
    rw [hJL, halfLineLaplace_const g hs, sub_self]
  intro t ht
  exact sub_eq_zero.mp (eq_zero_of_halfLineLaplace_eq_zero_of_damped_bound
    (fun t => J t - g) (hJ.sub continuousOn_const) 1 hb
      (fun s hs => hRL s (lt_trans zero_lt_one hs)) t ht)

end KVApproximation.Analysis
