module

public import KVApproximation.Analysis.VectorSobolev
public import TauCeti.Analysis.Sobolev.W1p.Zero

/-!
# Divergence-free fields and Dirichlet tests

Classical integration by parts gives the compactly supported test identity.
The L² pairing is continuous in the Sobolev norm, so closure supplies all
zero-boundary tests.
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace Distributions Gradient

namespace KVApproximation.Analysis

private theorem integral_test_eq_zero {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} {q : PhysicalSpace d → PhysicalSpace d}
    (hq : ContDiff ℝ 1 q) (hq₂ : MemLp q 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (hdiv : ∀ x ∈ (Ω : Set (PhysicalSpace d)),
      (∑ j, (fderiv ℝ q x (EuclideanSpace.single j 1)) j) = 0)
    (φ : 𝓓(Ω, ℝ)) :
    (∫ x in (Ω : Set (PhysicalSpace d)), ⟪q x, ∇ (φ : PhysicalSpace d → ℝ) x⟫_ℝ) = 0 := by
  let e (j : Fin d) : PhysicalSpace d := EuclideanSpace.single j 1
  have hg : MemLp (∇ (φ : PhysicalSpace d → ℝ)) 2
      (volume.restrict (Ω : Set (PhysicalSpace d))) :=
    (Lp.memLp (TauCeti.gradientTestFunctionLp (mu := volume) 2 φ)).ae_eq
      (TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ)
  have hleft (j : Fin d) : Integrable (fun x =>
      q x j * (∇ (φ : PhysicalSpace d → ℝ) x) j)
      (volume.restrict (Ω : Set (PhysicalSpace d))) :=
    memLp_one_iff_integrable.mp ((hq₂.eval_piLp j).mul (hg.eval_piLp j))
  have hright (j : Fin d) : Integrable (fun x => φ x * (fderiv ℝ q x (e j)) j)
      (volume.restrict (Ω : Set (PhysicalSpace d))) := by
    have hc : Continuous (fun x => (fderiv ℝ q x (e j)) j) :=
      (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).comp
        ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    exact (TauCeti.integrable_smul_of_locallyIntegrableOn
      (μ := volume) (hc.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) φ).integrableOn
  have hparts (j : Fin d) :
      (∫ x in (Ω : Set (PhysicalSpace d)), q x j * (∇ (φ : PhysicalSpace d → ℝ) x) j) =
        -(∫ x in (Ω : Set (PhysicalSpace d)), φ x * (fderiv ℝ q x (e j)) j) := by
    let P := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) j
    let f : PhysicalSpace d → ℝ := fun x => q x j
    have hf : ContDiff ℝ 1 f := P.contDiff.comp hq
    have hw := TauCeti.hasWeakFDerivOn_of_differentiableOn (μ := volume) (Ω := Ω)
      (hf.continuous.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
      ((hf.continuous_fderiv one_ne_zero).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
      (fun x _ => hf.differentiable one_ne_zero x)
    have hd (x : PhysicalSpace d) : fderiv ℝ f x (e j) = (fderiv ℝ q x (e j)) j := by
      change fderiv ℝ (P ∘ q) x (e j) = _
      rw [(P.hasFDerivAt.comp x (hq.differentiable one_ne_zero x).hasFDerivAt).fderiv]
      rfl
    have hφ (x : PhysicalSpace d) :
        lineDeriv ℝ (φ : PhysicalSpace d → ℝ) x (e j) =
          (∇ (φ : PhysicalSpace d → ℝ) x) j := by
      rw [(φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv,
        ← inner_gradient_left]
      simp only [e, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    calc
      _ = ∫ x in (Ω : Set (PhysicalSpace d)),
          lineDeriv ℝ (φ : PhysicalSpace d → ℝ) x (e j) • f x := by
        simp only [hφ, smul_eq_mul, f, mul_comm]
      _ = ∫ x, lineDeriv ℝ (φ : PhysicalSpace d → ℝ) x (e j) • f x :=
        TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ (e j)
      _ = -(∫ x, φ x • fderiv ℝ f x (e j)) :=
        ((TauCeti.hasWeakFDerivOn_iff.mp hw) (e j)).integral_lineDeriv_smul_eq_neg_integral_smul φ
      _ = -(∫ x in (Ω : Set (PhysicalSpace d)), φ x * (fderiv ℝ q x (e j)) j) := by
        rw [← TauCeti.setIntegral_smul_eq_integral_smul φ]
        simp only [hd, smul_eq_mul]
  calc
    _ = ∫ x in (Ω : Set (PhysicalSpace d)),
        ∑ j, q x j * (∇ (φ : PhysicalSpace d → ℝ) x) j := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
    _ = ∑ j, ∫ x in (Ω : Set (PhysicalSpace d)),
        q x j * (∇ (φ : PhysicalSpace d → ℝ) x) j :=
      integral_finsetSum _ (fun j _ => hleft j)
    _ = -(∑ j, ∫ x in (Ω : Set (PhysicalSpace d)),
        φ x * (fderiv ℝ q x (e j)) j) := by simp only [hparts, Finset.sum_neg_distrib]
    _ = -(∫ x in (Ω : Set (PhysicalSpace d)),
        φ x * ∑ j, (fderiv ℝ q x (e j)) j) := by
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ (fun j _ => hright j)]
    _ = 0 := by
      have hz : (∫ x in (Ω : Set (PhysicalSpace d)),
          φ x * ∑ j, (fderiv ℝ q x (e j)) j) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
        change φ x * (∑ j, (fderiv ℝ q x (EuclideanSpace.single j 1)) j) = 0
        rw [hdiv x hx, mul_zero]
      rw [hz, neg_zero]

/-- Theorem 3.1, static flux tests: a C¹ divergence-free L² vector
field annihilates the weak gradients of all scalar Dirichlet functions. -/
theorem integral_inner_gradient_eq_zero_of_divergence_eq_zero {d : ℕ}
    {Ω : Opens (PhysicalSpace d)} {q : PhysicalSpace d → PhysicalSpace d}
    (hq : ContDiff ℝ 1 q) (hq₂ : MemLp q 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (hdiv : ∀ x ∈ (Ω : Set (PhysicalSpace d)),
      (∑ j, (fderiv ℝ q x (EuclideanSpace.single j 1)) j) = 0)
    (v : TauCeti.W1p volume Ω 2) (hv : v ∈ TauCeti.w1p0Submodule volume Ω 2) :
    (∫ x in (Ω : Set (PhysicalSpace d)), ⟪q x, TauCeti.W1p.gradient v x⟫_ℝ) = 0 := by
  let Q := hq₂.toLp q
  have heq (w : TauCeti.W1p volume Ω 2) :
      (∫ x in (Ω : Set (PhysicalSpace d)), ⟪q x, TauCeti.W1p.gradient w x⟫_ℝ) =
        ⟪Q, TauCeti.W1p.gradientL w⟫_ℝ := by
    rw [TauCeti.W1p.gradientL_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hq₂.coeFn_toLp] with x hx
    rw [hx]
  rw [heq]
  refine TauCeti.w1p0Submodule_subset_of_isClosed (s := {w : TauCeti.W1p volume Ω 2 |
    ⟪Q, TauCeti.W1p.gradientL w⟫_ℝ = 0})
    (isClosed_eq (continuous_const.inner TauCeti.W1p.gradientL.continuous) continuous_const) ?_ hv
  intro φ
  change ⟪Q, TauCeti.W1p.gradientL (TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ)⟫_ℝ = 0
  rw [← heq, TauCeti.W1p.gradient_ofTestFunctionₗ]
  have hi : (∫ x in (Ω : Set (PhysicalSpace d)),
      ⟪q x, TauCeti.gradientTestFunctionLp (mu := volume) 2 φ x⟫_ℝ) =
        ∫ x in (Ω : Set (PhysicalSpace d)), ⟪q x, ∇ (φ : PhysicalSpace d → ℝ) x⟫_ℝ := by
    apply integral_congr_ae
    filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with x hx
    rw [hx]
  rw [hi]
  exact integral_test_eq_zero hq hq₂ hdiv φ

end KVApproximation.Analysis
