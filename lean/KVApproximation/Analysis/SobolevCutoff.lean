module

public import KVApproximation.Analysis.SobolevCutoffMap

/-!
# Cutoff products and zero boundary values

The bounded jet multiplier agrees with the classical product rule on
smooth fields. Closure then preserves the actual zero-boundary space.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions Gradient ENNReal

namespace KVApproximation.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- Theorem 3.1, cutoff product rule: the bounded jet operator has the
pointwise value and full-gradient formula almost everywhere. -/
theorem cutoffJetL_apply_ae (χ : 𝓓(Ω, ℝ)) (J : TauCeti.Sobolev1JetLp μ Ω 2) :
    cutoffJetL χ J =ᵐ[μ.restrict (Ω : Set E)] fun x =>
      WithLp.toLp 2 (χ x * WithLp.fst (J x),
        χ x • WithLp.snd (J x) + WithLp.fst (J x) • ∇ (χ : E → ℝ) x) := by
  let ν := μ.restrict (Ω : Set E)
  let a := TauCeti.testFunctionLp (mu := μ) ⊤ χ
  let b := TauCeti.gradientTestFunctionLp (mu := μ) ⊤ χ
  let V := TauCeti.Sobolev1JetLp.value J
  let G := TauCeti.Sobolev1JetLp.gradient J
  let A := (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holder 2 a V
  let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holder 2 a G
  let C := (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip.holder 2 b V
  let I₀ := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ ℝ E)
  let I₁ := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ ℝ E)
  have heq : cutoffJetL χ J = I₀.compLpL 2 ν A + I₁.compLpL 2 ν (B + C) := by
    simp only [cutoffJetL, add_apply, ContinuousLinearMap.comp_apply,
      TauCeti.Sobolev1JetLp.valueL_apply, TauCeti.Sobolev1JetLp.gradientL_apply,
      ContinuousLinearMap.holderL_apply_apply, ν, a, b, V, G, A, B, C, I₀, I₁]
  rw [heq]
  filter_upwards [Lp.coeFn_add (I₀.compLpL 2 ν A) (I₁.compLpL 2 ν (B + C)),
    I₀.coeFn_compLpL A, I₁.coeFn_compLpL (B + C), Lp.coeFn_add B C,
    (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 2) a V,
    (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).coeFn_holder (r := 2) a G,
    (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip.coeFn_holder (r := 2) b V,
    TauCeti.testFunctionLp_apply_ae (mu := μ) ⊤ χ,
    TauCeti.gradientTestFunctionLp_apply_ae (mu := μ) ⊤ χ,
    TauCeti.Sobolev1JetLp.value_apply_ae J,
    TauCeti.Sobolev1JetLp.gradient_apply_ae J]
    with x hadd hI₀ hI₁ hBC hA hB hC ha hb hV hG
  rw [hadd, Pi.add_apply, hI₀, hI₁, hBC, Pi.add_apply]
  change WithLp.toLp 2 (A x, (0 : E)) + WithLp.toLp 2 ((0 : ℝ), B x + C x) = _
  rw [hA, hB, hC]
  change WithLp.toLp 2 (a x * V x, (0 : E)) +
    WithLp.toLp 2 ((0 : ℝ), a x • G x + V x • b x) = _
  rw [ha, hb, hV, hG]
  simp only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem gradient_mul_smooth (χ : 𝓓(Ω, ℝ)) {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : E) :
    ∇ (fun y => χ y * f y) x = χ x • ∇ f x + f x • ∇ (χ : E → ℝ) x := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradient_left, inner_gradient_left, inner_gradient_left]
  change (fderiv ℝ ((χ : E → ℝ) * f) x) y = _
  rw [fderiv_mul (χ.contDiff.differentiable (by simp) x) (hf.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- Theorem 3.1, compactly supported tests: a cutoff of a smooth jet
is represented by an actual zero-boundary Sobolev function. -/
theorem cutoffJetL_mem_of_smooth (χ : 𝓓(Ω, ℝ))
    (J : TauCeti.Sobolev1JetLp μ Ω 2) {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hv : TauCeti.Sobolev1JetLp.value J =ᵐ[μ.restrict (Ω : Set E)] f)
    (hg : TauCeti.Sobolev1JetLp.gradient J =ᵐ[μ.restrict (Ω : Set E)] ∇ f) :
    cutoffJetL χ J ∈ Subtype.val ''
      (TauCeti.w1p0Submodule μ Ω 2 : Set (TauCeti.W1p μ Ω 2)) := by
  let φ : 𝓓(Ω, ℝ) := ⟨fun x => χ x * f x, χ.contDiff.mul hf,
    χ.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans χ.tsupport_subset⟩
  let v := TauCeti.W1p.ofTestFunctionₗ μ Ω 2 φ
  refine ⟨v, TauCeti.W1p.ofTestFunctionₗ_mem_w1p0Submodule φ, ?_⟩
  apply TauCeti.Sobolev1JetLp.ext
  · apply Lp.ext
    have hvφ : TauCeti.Sobolev1JetLp.value (v : TauCeti.Sobolev1JetLp μ Ω 2) =
        TauCeti.testFunctionLp (mu := μ) 2 φ := by
      rw [← TauCeti.W1p.value_coe, TauCeti.W1p.value_ofTestFunctionₗ]
    rw [hvφ]
    filter_upwards [TauCeti.testFunctionLp_apply_ae (mu := μ) 2 φ,
      TauCeti.Sobolev1JetLp.value_apply_ae (cutoffJetL χ J), cutoffJetL_apply_ae χ J,
      TauCeti.Sobolev1JetLp.value_apply_ae J, hv] with x hφ hc hcut hJ hvalue
    rw [hφ, hc, hcut]
    change χ x * f x = χ x * WithLp.fst (J x)
    rw [← hJ, hvalue]
  · apply Lp.ext
    have hgφ : TauCeti.Sobolev1JetLp.gradient (v : TauCeti.Sobolev1JetLp μ Ω 2) =
        TauCeti.gradientTestFunctionLp (mu := μ) 2 φ := by
      rw [← TauCeti.W1p.gradient_coe, TauCeti.W1p.gradient_ofTestFunctionₗ]
    rw [hgφ]
    filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := μ) 2 φ,
      TauCeti.Sobolev1JetLp.gradient_apply_ae (cutoffJetL χ J), cutoffJetL_apply_ae χ J,
      TauCeti.Sobolev1JetLp.value_apply_ae J,
      TauCeti.Sobolev1JetLp.gradient_apply_ae J, hv, hg]
      with x hφ hc hcut hJv hJg hvalue hgradient
    rw [hφ, hc, hcut]
    change ∇ (fun y => χ y * f y) x =
      χ x • WithLp.snd (J x) + WithLp.fst (J x) • ∇ (χ : E → ℝ) x
    rw [← hJv, ← hJg, hvalue, hgradient]
    exact gradient_mul_smooth χ hf x

/-- Theorem 3.1, localized weak tests: smooth cutoff multiplication
preserves the zero-boundary Sobolev space on any open domain. -/
theorem cutoffJetL_mem_of_zeroBoundary (χ : 𝓓(Ω, ℝ)) (u : TauCeti.W1p μ Ω 2)
    (hu : u ∈ TauCeti.w1p0Submodule μ Ω 2) :
    cutoffJetL χ (u : TauCeti.Sobolev1JetLp μ Ω 2) ∈ Subtype.val ''
      (TauCeti.w1p0Submodule μ Ω 2 : Set (TauCeti.W1p μ Ω 2)) := by
  have hclosed : IsClosed
      (Subtype.val '' (TauCeti.w1p0Submodule μ Ω 2 : Set (TauCeti.W1p μ Ω 2))) :=
    (TauCeti.w1pSubmodule μ Ω 2).isClosed.isClosedEmbedding_subtypeVal.isClosedMap _
      (TauCeti.w1p0Submodule μ Ω 2).isClosed
  have hcont : Continuous fun w : TauCeti.W1p μ Ω 2 =>
      cutoffJetL χ (w : TauCeti.Sobolev1JetLp μ Ω 2) :=
    (cutoffJetL χ).continuous.comp continuous_subtype_val
  refine TauCeti.w1p0Submodule_subset_of_isClosed (hclosed.preimage hcont) ?_ hu
  intro φ
  apply cutoffJetL_mem_of_smooth χ _ φ.contDiff
  · rw [← TauCeti.W1p.value_coe, TauCeti.W1p.value_ofTestFunctionₗ]
    exact TauCeti.testFunctionLp_apply_ae (mu := μ) 2 φ
  · rw [← TauCeti.W1p.gradient_coe, TauCeti.W1p.gradient_ofTestFunctionₗ]
    exact TauCeti.gradientTestFunctionLp_apply_ae (mu := μ) 2 φ

end KVApproximation.Analysis
