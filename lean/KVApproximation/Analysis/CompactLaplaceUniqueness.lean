module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Uniqueness from compactly supported exponential moments
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Compact support permits tests that are only continuous on the interval. -/
private theorem integrable_on_supported_interval {a b : ℝ} (ρ : Measure ℝ)
    [IsFiniteMeasure ρ] (hρ : ρ (Set.Icc a b)ᶜ = 0) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) : Integrable f ρ := by
  have hi := hf.integrableOn_Icc (μ := ρ)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hρ)] at hi

/-- Proposition 3.3, uniqueness bridge: on a positive compact interval,
the weighted exponential moments at nonnegative integer times determine a
finite positive measure. -/
theorem measure_eq_of_weighted_exponential_moments {a b : ℝ} (ha : 0 < a)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Set.Icc a b)ᶜ = 0) (hν : ν (Set.Icc a b)ᶜ = 0)
    (hmom : ∀ n : ℕ, (∫ r, r * (Real.exp (-r)) ^ n ∂μ) =
      ∫ r, r * (Real.exp (-r)) ^ n ∂ν) : μ = ν := by
  let q : C(ℝ, ℝ) := ⟨fun r => Real.exp (-r), by fun_prop⟩
  let A : Subalgebra ℝ C(ℝ, ℝ) := Algebra.adjoin ℝ {q}
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    refine ⟨q, ⟨q, Algebra.subset_adjoin (Set.mem_singleton q), rfl⟩, ?_⟩
    intro heq
    exact hxy (neg_injective (Real.exp_injective heq))
  have hint (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hρ : ρ (Set.Icc a b)ᶜ = 0)
      (p : Polynomial ℝ) : Integrable (fun r => r * p.eval (q r)) ρ :=
    integrable_on_supported_interval ρ hρ (by fun_prop)
  have hpoly (p : Polynomial ℝ) :
      (∫ r, r * p.eval (q r) ∂μ) = ∫ r, r * p.eval (q r) ∂ν := by
    induction p using Polynomial.induction_on' with
    | add p s hp hs =>
      simp_rw [Polynomial.eval_add, mul_add]
      rw [integral_add (hint μ hμ p) (hint μ hμ s),
        integral_add (hint ν hν p) (hint ν hν s), hp, hs]
    | monomial n c =>
      simp only [Polynomial.eval_monomial]
      have heq : (fun r => r * (c * q r ^ n)) = fun r => c * (r * q r ^ n) := by
        funext r
        ring
      rw [heq, integral_const_mul, integral_const_mul]
      exact congrArg (c * ·) (hmom n)
  have halgebra (p : C(ℝ, ℝ)) (hp : p ∈ A) :
      (∫ r, r * p r ∂μ) = ∫ r, r * p r ∂ν := by
    obtain ⟨s, hs⟩ := Algebra.adjoin_mem_exists_aeval ℝ q hp
    rw [← hs]
    simpa only [Polynomial.aeval_continuousMap_apply] using hpoly s
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : C(ℝ, ℝ) := ⟨fun r => f r / max a r,
    f.continuous.div (continuous_const.max continuous_id)
      (fun r => (ha.trans_le (le_max_left _ _)).ne')⟩
  have hfg (r : ℝ) (hr : r ∈ Set.Icc a b) : r * g r = f r := by
    change r * (f r / max a r) = f r
    rw [max_eq_right hr.1]
    exact mul_div_cancel₀ _ (ha.trans_le hr.1).ne'
  let D := |a| + |b| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hrD (r : ℝ) (hr : r ∈ Set.Icc a b) : |r| ≤ D := by
    apply abs_le.2
    constructor
    · have hn := neg_abs_le a
      dsimp [D]
      linarith [abs_nonneg b, hr.1]
    · have hn := le_abs_self b
      dsimp [D]
      linarith [abs_nonneg a, hr.2]
  apply eq_of_forall_dist_le
  intro ε hε
  let N := μ.real Set.univ + ν.real Set.univ + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let δ := ε / (D * N)
  have hδ : 0 < δ := div_pos hε (mul_pos hD hN)
  obtain ⟨p, hpA, hp⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hsep g isCompact_Icc hδ
  have herr (r : ℝ) (hr : r ∈ Set.Icc a b) : |f r - r * p r| ≤ D * δ := by
    rw [← hfg r hr, ← mul_sub, abs_mul]
    have he : |g r - p r| ≤ δ := by
      simpa only [Real.norm_eq_abs, abs_sub_comm] using (hp r hr).le
    exact mul_le_mul (hrD r hr) he (abs_nonneg _) hD.le
  have herror (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hρ : ρ (Set.Icc a b)ᶜ = 0) :
      |(∫ r, f r ∂ρ) - ∫ r, r * p r ∂ρ| ≤ D * δ * ρ.real Set.univ := by
    have hfρ : Integrable (fun r => f r) ρ := f.integrable (μ := ρ)
    have hpρ : Integrable (fun r => r * p r) ρ :=
      integrable_on_supported_interval ρ hρ (by fun_prop)
    rw [← integral_sub hfρ hpρ, ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le_const
    filter_upwards [ae_iff.mpr hρ] with r hr
    exact herr r hr
  have hpint := halgebra p hpA
  calc
    dist (∫ r, f r ∂μ) (∫ r, f r ∂ν) ≤
        dist (∫ r, f r ∂μ) (∫ r, r * p r ∂μ) +
        dist (∫ r, r * p r ∂ν) (∫ r, f r ∂ν) := by
      rw [← hpint]
      exact dist_triangle _ _ _
    _ ≤ D * δ * μ.real Set.univ + D * δ * ν.real Set.univ := by
      apply add_le_add (herror μ hμ)
      simpa only [Real.dist_eq, abs_sub_comm] using herror ν hν
    _ ≤ D * δ * N := by
      dsimp [N]
      nlinarith [mul_nonneg hD.le hδ.le]
    _ = ε := by
      dsimp [δ]
      field_simp [hD.ne', hN.ne']


end KVApproximation.Analysis
