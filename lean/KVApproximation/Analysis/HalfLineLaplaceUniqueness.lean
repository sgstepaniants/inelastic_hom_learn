module

public import KVApproximation.Analysis.HalfLineLaplaceProperties
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Injectivity of the half-line Laplace transform
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, Laplace uniqueness: nonnegative times are mapped
into the compact interval used for polynomial approximation. -/
private theorem exp_neg_mem_unit {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)⟩

/-- Theorem 3.1, Laplace uniqueness: bounded continuous tests of
exp(-t) preserve integrability against the exponentially weighted trajectory. -/
private theorem integrable_laplace_test
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖h t‖ ≤ M)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * h t * g (Real.exp (-t)))
      (Set.Ioi (0 : ℝ)) := by
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hM : 0 ≤ M := (norm_nonneg (h 0)).trans (hbound 0 le_rfl)
  have hc : ContinuousOn (fun t : ℝ => h t * g (Real.exp (-t)))
      (Set.Ici (0 : ℝ)) :=
    hcont.mul (hg.comp (by fun_prop) (fun t ht => exp_neg_mem_unit ht))
  have hb (t : ℝ) (ht : 0 ≤ t) : ‖h t * g (Real.exp (-t))‖ ≤ M * N := by
    rw [norm_mul]
    exact mul_le_mul (hbound t ht) (hN _ (exp_neg_mem_unit ht)) (norm_nonneg _) hM
  have hi := integrable_halfLineLaplace (fun t : ℝ => h t * g (Real.exp (-t)))
    hc hb (s := 1) zero_lt_one
  simpa only [neg_one_mul, smul_eq_mul, mul_assoc] using hi

/-- Theorem 3.1, Laplace uniqueness: integer rates annihilate
every polynomial in exp(-t), with integrability before each integral split. -/
private theorem integral_laplace_polynomial_eq_zero
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖h t‖ ≤ M)
    (hmom : ∀ n : ℕ, halfLineLaplace h ((n : ℝ) + 1) = 0)
    (p : Polynomial ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * h t * p.eval (Real.exp (-t))) = 0 := by
  have hint (q : Polynomial ℝ) :=
    integrable_laplace_test h hcont hbound q.eval q.continuous.continuousOn
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp_rw [Polynomial.eval_add, mul_add]
    rw [integral_add (hint p) (hint q), hp, hq, add_zero]
  | monomial n c =>
    have heq : (fun t : ℝ => Real.exp (-t) * h t *
        (Polynomial.monomial n c).eval (Real.exp (-t))) =
        fun t : ℝ => c * (Real.exp (-((n : ℝ) + 1) * t) * h t) := by
      funext t
      rw [Polynomial.eval_monomial]
      calc
        _ = c * ((Real.exp (-t) * Real.exp (-t) ^ n) * h t) := by ring
        _ = _ := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 3
          ring
    have hn := hmom n
    change (∫ t in Set.Ioi (0 : ℝ), Real.exp (-((n : ℝ) + 1) * t) * h t) = 0 at hn
    rw [heq, integral_const_mul, hn, mul_zero]

/-- Theorem 3.1, Laplace uniqueness: the factor x makes the
bounded trajectory test continuous at the compactification endpoint. -/
private theorem continuousOn_logarithmic_test
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖h t‖ ≤ M) :
    ContinuousOn (fun x : ℝ => x * h (-Real.log x)) (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    change Tendsto (fun y : ℝ => y * h (-Real.log y))
      (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 (0 * h (-Real.log 0)))
    rw [zero_mul]
    apply squeeze_zero_norm' (a := fun y : ℝ => y * M)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hy.1]
      exact mul_le_mul_of_nonneg_left
        (hbound _ (neg_nonneg.mpr (Real.log_nonpos hy.1 hy.2))) hy.1
    · have hy : Tendsto (fun y : ℝ => y) (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [zero_mul] using hy.mul_const M
  · have hlog : ContinuousWithinAt (fun y : ℝ => -Real.log y)
        (Set.Icc (0 : ℝ) 1) x :=
      (Real.continuousAt_log hx0).neg.continuousWithinAt
    exact continuousWithinAt_id.mul
      ((hcont _ (neg_nonneg.mpr (Real.log_nonpos hx.1 hx.2))).comp
        (f := fun y : ℝ => -Real.log y) hlog
        (fun y hy => neg_nonneg.mpr (Real.log_nonpos hy.1 hy.2)))

/-- Theorem 3.1, injectivity of the time-domain Laplace transform:
positive integer rates determine a bounded continuous scalar trajectory
on the entire nonnegative time axis, including its initial value. -/
theorem eq_zero_of_halfLineLaplace_nat_eq_zero
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖h t‖ ≤ M)
    (hmom : ∀ n : ℕ, halfLineLaplace h ((n : ℝ) + 1) = 0) :
    ∀ t : ℝ, 0 ≤ t → h t = 0 := by
  let g (x : ℝ) := x * h (-Real.log x)
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    continuousOn_logarithmic_test h hcont hbound
  have hM : 0 ≤ M := (norm_nonneg (h 0)).trans (hbound 0 le_rfl)
  have hintg := integrable_laplace_test h hcont hbound g hg
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi (0 : ℝ)) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have hexpInt : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t)) = 1 := by
    simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have hzero : (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-t) * h t * g (Real.exp (-t))) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    have hM1 : 0 < M + 1 := by linarith
    let δ := ε / (M + 1)
    have hδ : 0 < δ := div_pos hε hM1
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg δ hδ
    have hintp := integrable_laplace_test h hcont hbound p.eval p.continuous.continuousOn
    have hpzero := integral_laplace_polynomial_eq_zero h hcont hbound hmom p
    have heq : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * h t *
        (g (Real.exp (-t)) - p.eval (Real.exp (-t)))) =
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * h t * g (Real.exp (-t)) := by
      simp_rw [mul_sub]
      rw [integral_sub hintg hintp, hpzero, sub_zero]
    rw [← heq, zero_add]
    calc
      _ ≤ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * (M * δ) := by
        apply norm_integral_le_of_norm_le (hexp.mul_const (M * δ))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have herr : ‖g (Real.exp (-t)) - p.eval (Real.exp (-t))‖ ≤ δ := by
          simpa only [Real.norm_eq_abs, abs_sub_comm] using
            (hp _ (exp_neg_mem_unit ht.le)).le
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        calc
          _ ≤ (Real.exp (-t) * M) * δ :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left (hbound t ht.le) (Real.exp_pos _).le)
              herr (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hM)
          _ = _ := mul_assoc _ _ _
      _ = M * δ := by rw [integral_mul_const, hexpInt, one_mul]
      _ ≤ (M + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε := by dsimp [δ]; field_simp
  have hgexp (t : ℝ) : g (Real.exp (-t)) = Real.exp (-t) * h t := by
    dsimp only [g]
    rw [Real.log_exp, neg_neg]
  have hnonneg : 0 ≤ fun t : ℝ => Real.exp (-t) * h t * g (Real.exp (-t)) := by
    intro t
    change 0 ≤ Real.exp (-t) * h t * g (Real.exp (-t))
    rw [hgexp]
    exact mul_self_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hintg).mp hzero
  have hh : h =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] 0 := by
    filter_upwards [hae] with t ht
    have hprod : Real.exp (-t) * h t = 0 :=
      mul_self_eq_zero.mp (by simpa only [hgexp, Pi.zero_apply] using ht)
    exact (mul_eq_zero.mp hprod).resolve_left (Real.exp_pos _).ne'
  rw [restrict_Ioi_eq_restrict_Ici] at hh
  exact Measure.eqOn_of_ae_eq (s := Set.Ici (0 : ℝ)) hh hcont continuousOn_const (by
    rw [interior_Ici, closure_Ioi])

/-- Theorem 3.1, identification of the homogeneous limit:
bounded continuous Banach-valued trajectories with equal positive-rate
Laplace transforms agree at every nonnegative time. -/
theorem eqOn_of_halfLineLaplace_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (u v : ℝ → F) (hu : ContinuousOn u (Set.Ici (0 : ℝ)))
    (hv : ContinuousOn v (Set.Ici (0 : ℝ))) {Mu Mv : ℝ}
    (huBound : ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ Mu)
    (hvBound : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ Mv)
    (hLap : ∀ s : ℝ, 0 < s → halfLineLaplace u s = halfLineLaplace v s) :
    Set.EqOn u v (Set.Ici (0 : ℝ)) := by
  intro t ht
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ℓ
  let h (r : ℝ) := ℓ (u r) - ℓ (v r)
  have hc : ContinuousOn h (Set.Ici (0 : ℝ)) :=
    (ℓ.continuous.comp_continuousOn hu).sub (ℓ.continuous.comp_continuousOn hv)
  have hb (r : ℝ) (hr : 0 ≤ r) : ‖h r‖ ≤ ‖ℓ‖ * (Mu + Mv) := by
    calc
      _ ≤ ‖ℓ (u r)‖ + ‖ℓ (v r)‖ := norm_sub_le _ _
      _ ≤ ‖ℓ‖ * Mu + ‖ℓ‖ * Mv := add_le_add
        ((ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (huBound r hr) (norm_nonneg ℓ)))
        ((ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hvBound r hr) (norm_nonneg ℓ)))
      _ = _ := (mul_add _ _ _).symm
  have hm (n : ℕ) : halfLineLaplace h ((n : ℝ) + 1) = 0 := by
    let s : ℝ := (n : ℝ) + 1
    have hs : 0 < s := by dsimp [s]; positivity
    have hiu := integrable_halfLineLaplace u hu huBound hs
    have hiv := integrable_halfLineLaplace v hv hvBound hs
    have hℓu := ℓ.integrable_comp hiu
    have hℓv := ℓ.integrable_comp hiv
    simp only [map_smul, smul_eq_mul] at hℓu hℓv
    have hcu := ℓ.integral_comp_comm hiu
    have hcv := ℓ.integral_comp_comm hiv
    simp only [map_smul, smul_eq_mul] at hcu hcv
    change (∫ r in Set.Ioi (0 : ℝ), Real.exp (-s * r) * (ℓ (u r) - ℓ (v r))) = 0
    simp_rw [mul_sub]
    rw [integral_sub hℓu hℓv]
    exact sub_eq_zero.mpr (hcu.trans ((congrArg ℓ (hLap s hs)).trans hcv.symm))
  exact sub_eq_zero.mp (eq_zero_of_halfLineLaplace_nat_eq_zero h hc hb hm t ht)

end KVApproximation.Analysis
