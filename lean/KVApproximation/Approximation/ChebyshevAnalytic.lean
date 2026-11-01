module

public import KVApproximation.Approximation.ChebyshevCoefficients
public import KVApproximation.Approximation.BernsteinGeometry
public import KVApproximation.Analysis.AnnulusCoefficientBounds
public import KVApproximation.Analysis.CircleFourier
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Analytic Chebyshev coefficients
-/

public section

namespace KVApproximation.Approximation

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Lemma B.9, proof: pull back analyticity from the ellipse to the outer annulus. -/
private theorem analytic_joukowski_annulus {f : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ)) :
    AnalyticOnNhd ℂ (f ∘ Analysis.joukowski) (Metric.closedBall 0 ρ \ Metric.ball 0 1) := by
  intro w hw
  have hnorm : 1 ≤ ‖w‖ ∧ ‖w‖ ≤ ρ := by
    simpa only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt, and_comm] using hw
  have hwne : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hnorm.1)
  have hj : AnalyticAt ℂ Analysis.joukowski w := by
    unfold Analysis.joukowski
    exact (analyticAt_id.add (analyticAt_id.inv hwne)).div_const
  apply (hf _ (joukowski_mem_bernsteinEllipse hρ ⟨?_, hnorm.2⟩)).comp hj
  exact ((inv_le_one₀ (lt_trans zero_lt_one hρ)).mpr hρ.le).trans hnorm.1

/-- Lemma B.9, proof: deform each nonnegative Laurent coefficient to the
outer circle and apply the sharp contour estimate. -/
private theorem norm_joukowski_coefficient_le {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ))
    (hbound : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) (k : ℕ) :
    ‖Analysis.circleCoefficient (f ∘ Analysis.joukowski) 1 k‖ ≤ M / ρ ^ k := by
  rw [← Analysis.circleCoefficient_eq_of_analyticOnNhd zero_lt_one hρ.le
    (analytic_joukowski_annulus hρ hf) k]
  apply Analysis.norm_circleCoefficient_le (lt_trans zero_lt_one hρ)
  intro w hw
  have hnorm : ‖w‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
  apply hbound _ (joukowski_mem_bernsteinEllipse hρ ?_)
  rw [hnorm]
  exact ⟨((inv_le_one₀ (lt_trans zero_lt_one hρ)).mpr hρ.le).trans hρ.le, le_rfl⟩

/-- Lemma B.9, proof: analyticity on a Bernstein ellipse gives geometric
decay of the scalar Chebyshev coefficients. -/
theorem norm_chebyshevCoefficient_le {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ))
    (hbound : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) (k : ℕ) :
    ‖chebyshevCoefficient f k‖ ≤ 2 * M / ρ ^ k := by
  have hk := norm_joukowski_coefficient_le hρ hf hbound k
  by_cases hkzero : k = 0
  · subst k
    simp only [chebyshevCoefficient, ↓reduceIte, pow_zero, div_one] at hk ⊢
    linarith
  · simp only [chebyshevCoefficient, hkzero, ↓reduceIte, norm_mul, Complex.norm_ofNat]
    calc
      _ ≤ 2 * (M / ρ ^ k) := mul_le_mul_of_nonneg_left hk (by norm_num)
      _ = _ := by ring

/-- Lemma B.9, proof: opposite Fourier modes pair to a Chebyshev mode. -/
private theorem paired_fourier_modes (k : ℕ) (θ : ℝ) :
    fourier (k : ℤ) (θ : AddCircle (2 * Real.pi)) +
      fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) =
      2 * (((Polynomial.Chebyshev.T ℝ k).eval (Real.cos θ) : ℝ) : ℂ) := by
  have hmode (n : ℤ) : fourier n (θ : AddCircle (2 * Real.pi)) =
      Complex.exp ((n : ℂ) * θ * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  rw [hmode, hmode, Polynomial.Chebyshev.T_real_cos]
  simp only [Int.cast_neg, Int.cast_natCast, Complex.ofReal_cos,
    Complex.ofReal_mul, Complex.ofReal_natCast, neg_mul]
  simpa only [neg_mul] using (Complex.two_cos ((k : ℂ) * θ)).symm

/-- Lemma B.9, proof: the Chebyshev series of an analytic scalar function
converges to it throughout the closed reference interval. -/
theorem hasSum_chebyshevSeries {f : ℂ → ℂ} {ρ M : ℝ}
    (hρ : 1 < ρ) (_hM : 0 ≤ M)
    (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ))
    (hbound : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    HasSum (fun k => chebyshevCoefficient f k *
      (((Polynomial.Chebyshev.T ℝ k).eval x : ℝ) : ℂ)) (f x) := by
  have hreal (t : AddCircle (2 * Real.pi)) :
      (t.toCircle : ℂ).re ∈ Set.Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    simpa only [Circle.norm_coe] using Complex.abs_re_le_norm (t.toCircle : ℂ)
  let g : C(AddCircle (2 * Real.pi), ℂ) :=
    { toFun := fun t => f (((t.toCircle : ℂ).re : ℝ) : ℂ)
      continuous_toFun := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact (hf _ (real_mem_bernsteinEllipse hρ (hreal t))).continuousAt.comp
          (f := fun s : AddCircle (2 * Real.pi) => (((s.toCircle : ℂ).re : ℝ) : ℂ))
          (by fun_prop) }
  have hg_eq (t : AddCircle (2 * Real.pi)) :
      g t = (f ∘ Analysis.joukowski) (t.toCircle : ℂ) := by
    rw [Function.comp_apply, Analysis.joukowski_unit (Circle.norm_coe _)]
    rfl
  have hg_even (t : AddCircle (2 * Real.pi)) : g (-t) = g t := by
    rw [hg_eq, hg_eq]
    simp only [Function.comp_apply, AddCircle.toCircle_neg, Circle.coe_inv,
      Analysis.joukowski_inv]
  have ha (k : ℕ) : fourierCoeff g (k : ℤ) =
      Analysis.circleCoefficient (f ∘ Analysis.joukowski) 1 k := by
    rw [Analysis.circleCoefficient_eq_fourierCoeff]
    apply congrArg (fun v : AddCircle (2 * Real.pi) → ℂ => fourierCoeff v (k : ℤ))
    funext t
    exact hg_eq t
  have hρpos := lt_trans zero_lt_one hρ
  have hgeom : Summable (fun k : ℕ => M / ρ ^ k) := by
    simpa only [div_eq_mul_inv, inv_pow] using
      (summable_geometric_of_lt_one (inv_nonneg.mpr hρpos.le)
        ((inv_lt_one₀ hρpos).mpr hρ)).mul_left M
  have hnat : Summable (fun k : ℕ => fourierCoeff g (k : ℤ)) := by
    apply hgeom.of_norm_bounded
    intro k
    rw [ha]
    exact norm_joukowski_coefficient_le hρ hf hbound k
  have hneg : Summable (fun k : ℕ => fourierCoeff g (-(k + 1 : ℤ))) := by
    simp_rw [Analysis.fourierCoeff_neg_of_even hg_even]
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hnat
  have hall : Summable (fourierCoeff g) := hnat.of_nat_of_neg_add_one hneg
  let θ := Real.arccos x
  have hcos : Real.cos θ = x := Real.cos_arccos hx.1 hx.2
  have hgθ : g (θ : AddCircle (2 * Real.pi)) = f x := by
    change f (((AddCircle.toCircle (θ : AddCircle (2 * Real.pi)) : ℂ).re : ℝ) : ℂ) = f x
    simp only [AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul,
      Circle.coe_exp, Complex.exp_ofReal_mul_I_re, hcos]
  have hsum := has_pointwise_sum_fourier_series_of_summable hall (θ : AddCircle (2 * Real.pi))
  have hsingle : HasSum (fun k : ℕ => if k = 0 then fourierCoeff g 0 else 0)
      (fourierCoeff g 0) := hasSum_ite_eq 0 _
  have hpaired := hsum.nat_add_neg.sub hsingle
  simp only [hgθ, smul_eq_mul, fourier_zero, mul_one, add_sub_cancel_right] at hpaired
  apply hpaired.congr_fun
  intro k
  by_cases hk : k = 0
  · subst k
    simp only [chebyshevCoefficient, ↓reduceIte, Nat.cast_zero, neg_zero,
      Polynomial.Chebyshev.T_zero, Polynomial.eval_one, Complex.ofReal_one,
      fourier_zero, mul_one]
    simpa only [Nat.cast_zero, add_sub_cancel_right] using (ha 0).symm
  · simp only [chebyshevCoefficient, hk, ↓reduceIte, sub_zero]
    rw [Analysis.fourierCoeff_neg_of_even hg_even, ← mul_add, paired_fourier_modes, hcos, ha]
    ring

end KVApproximation.Approximation
