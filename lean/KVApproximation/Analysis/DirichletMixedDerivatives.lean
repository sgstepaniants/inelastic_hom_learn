module

public import KVApproximation.Analysis.SobolevDirectionalDerivative
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Mixed directional derivative identity
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace Distributions

namespace KVApproximation.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

omit [FiniteDimensional ℝ E] in
/-- Theorem 3.1, spatial coercivity: the directional L² map agrees
almost everywhere with the weak gradient paired with the direction. -/
theorem directionalDerivativeL_apply_ae (a : E) (u : TauCeti.W1p μ Ω 2) :
    ∀ᵐ x ∂μ.restrict (Ω : Set E),
      directionalDerivativeL μ Ω a u x = ⟪a, TauCeti.W1p.gradient u x⟫_ℝ := by
  have h := (innerSL ℝ a).coeFn_compLpL (p := 2)
    (μ := μ.restrict (Ω : Set E)) (TauCeti.W1p.gradientL u)
  filter_upwards [h] with x hx
  change (innerSL ℝ a).compLpL 2 (μ.restrict (Ω : Set E)) (TauCeti.W1p.gradientL u) x = _
  rw [hx, TauCeti.W1p.gradientL_apply]
  rfl

private theorem directional_test_ae (φ : 𝓓(Ω, ℝ)) (a : E) :
    ∀ᵐ x ∂μ.restrict (Ω : Set E),
      directionalDerivativeL μ Ω a (TauCeti.W1p.ofTestFunctionₗ μ Ω 2 φ) x =
        lineDeriv ℝ (φ : E → ℝ) x a := by
  have h := directionalDerivativeL_apply_ae a (TauCeti.W1p.ofTestFunctionₗ μ Ω 2 φ)
  rw [TauCeti.W1p.gradient_ofTestFunctionₗ] at h
  filter_upwards [h, TauCeti.gradientTestFunctionLp_apply_ae (mu := μ) 2 φ] with x hx hg
  rw [hx, hg, real_inner_comm, inner_gradient_left]
  exact ((φ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv.symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem lineDeriv_test_comm (φ : 𝓓(Ω, ℝ)) (a b x : E) :
    lineDeriv ℝ (TestFunction.lineDerivCLM ℝ a φ : 𝓓(Ω, ℝ)) x b =
      lineDeriv ℝ (TestFunction.lineDerivCLM ℝ b φ : 𝓓(Ω, ℝ)) x a := by
  have hφ := φ.contDiff.differentiable (by simp)
  have hd : Differentiable ℝ (fderiv ℝ (φ : E → ℝ)) :=
    (φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  have hfun (c : E) :
      (TestFunction.lineDerivCLM ℝ c φ : 𝓓(Ω, ℝ)) =
        (fun y => fderiv ℝ (φ : E → ℝ) y c : E → ℝ) := by
    funext y
    rw [TestFunction.lineDerivCLM_apply_of_le le_top]
    exact (hφ y).lineDeriv_eq_fderiv
  rw [hfun a, hfun b]
  have ha := (ContinuousLinearMap.apply ℝ ℝ a).hasFDerivAt.comp x (hd x).hasFDerivAt
  have hb := (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x (hd x).hasFDerivAt
  change lineDeriv ℝ ((ContinuousLinearMap.apply ℝ ℝ a) ∘ fderiv ℝ (φ : E → ℝ)) x b =
    lineDeriv ℝ ((ContinuousLinearMap.apply ℝ ℝ b) ∘ fderiv ℝ (φ : E → ℝ)) x a
  rw [(ha.hasLineDerivAt b).lineDeriv, (hb.hasLineDerivAt a).lineDeriv]
  exact (φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)).eq b a

private theorem inner_test_directional (φ : 𝓓(Ω, ℝ))
    (v : TauCeti.W1p μ Ω 2) (a b : E) :
    ⟪directionalDerivativeL μ Ω a (TauCeti.W1p.ofTestFunctionₗ μ Ω 2 φ),
      directionalDerivativeL μ Ω b v⟫_ℝ =
      ∫ x, lineDeriv ℝ (φ : E → ℝ) x a * ⟪b, TauCeti.W1p.gradient v x⟫_ℝ ∂μ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in (Ω : Set E),
        lineDeriv ℝ (φ : E → ℝ) x a * ⟪b, TauCeti.W1p.gradient v x⟫_ℝ ∂μ := by
      apply integral_congr_ae
      filter_upwards [directional_test_ae (μ := μ) φ a,
        directionalDerivativeL_apply_ae b v] with x hx hy
      simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]
    _ = _ := by
      simpa only [smul_eq_mul] using
        (TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul
          (μ := μ) (w := fun x => ⟪b, TauCeti.W1p.gradient v x⟫_ℝ) φ a)

private theorem inner_test_directional_ibp (φ : 𝓓(Ω, ℝ))
    (v : TauCeti.W1p μ Ω 2) (a b : E) :
    ⟪directionalDerivativeL μ Ω a (TauCeti.W1p.ofTestFunctionₗ μ Ω 2 φ),
      directionalDerivativeL μ Ω b v⟫_ℝ =
      -(∫ x, lineDeriv ℝ (TestFunction.lineDerivCLM ℝ a φ : 𝓓(Ω, ℝ)) x b *
        TauCeti.W1p.value v x ∂μ) := by
  rw [inner_test_directional]
  have hw0 := TauCeti.hasWeakFDerivOn_iff.mp (TauCeti.W1p.hasWeakFDerivOn v) b
  have hw := hw0.integral_lineDeriv_smul_eq_neg_integral_smul
    (TestFunction.lineDerivCLM ℝ a φ : 𝓓(Ω, ℝ))
  have heq : (∫ x, lineDeriv ℝ (φ : E → ℝ) x a * ⟪b, TauCeti.W1p.gradient v x⟫_ℝ ∂μ) =
      ∫ x, (TestFunction.lineDerivCLM ℝ a φ : 𝓓(Ω, ℝ)) x •
        innerSL ℝ (TauCeti.W1p.gradient v x) b ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [TestFunction.lineDerivCLM_apply_of_le le_top]
    simp only [smul_eq_mul, innerSL_apply_apply, real_inner_comm]
  rw [heq]
  simpa only [neg_neg, smul_eq_mul] using (congrArg Neg.neg hw).symm

/-- Theorem 3.1, Dirichlet Korn argument: integration by parts
interchanges directions in the L² pairing. Only the first scalar
Sobolev function needs zero boundary values. -/
theorem inner_directionalDerivative_swap (u v : TauCeti.W1p μ Ω 2)
    (hu : u ∈ TauCeti.w1p0Submodule μ Ω 2) (a b : E) :
    ⟪directionalDerivativeL μ Ω a u, directionalDerivativeL μ Ω b v⟫_ℝ =
      ⟪directionalDerivativeL μ Ω b u, directionalDerivativeL μ Ω a v⟫_ℝ := by
  apply TauCeti.w1p0Submodule_subset_of_isClosed (s := {w |
    ⟪directionalDerivativeL μ Ω a w, directionalDerivativeL μ Ω b v⟫_ℝ =
      ⟪directionalDerivativeL μ Ω b w, directionalDerivativeL μ Ω a v⟫_ℝ})
    (isClosed_eq ((directionalDerivativeL μ Ω a).continuous.inner continuous_const)
      ((directionalDerivativeL μ Ω b).continuous.inner continuous_const)) _ hu
  intro φ
  change ⟪_, _⟫_ℝ = ⟪_, _⟫_ℝ
  rw [inner_test_directional_ibp, inner_test_directional_ibp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [lineDeriv_test_comm φ a b x]

end KVApproximation.Analysis
