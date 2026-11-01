module

public import KVApproximation.Analysis.CutoffPairing
public import KVApproximation.Analysis.DirichletCutoff

/-!
# Localized stress identities

The full-gradient product rule separates the strain term from the
cutoff-gradient pairing. The splitting takes place in L², where both
pairings are integrable.
-/

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped Distributions Gradient InnerProductSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, localized test gradients: the bounded L² map has the
physical-coordinate outer-product representative. -/
theorem cutoffGradientL_apply_ae (χ : 𝓓(Ω, ℝ))
    (u : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    cutoffGradientL χ u =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      WithLp.toLp 2 (fun ij => u x ij.1 * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2) := by
  filter_upwards [(outerL d).flip.coeFn_holder (r := 2)
    (TauCeti.gradientTestFunctionLp (mu := volume) ⊤ χ) u,
    TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) ⊤ χ] with x hx hχ
  change (outerL d).flip.holder 2
    (TauCeti.gradientTestFunctionLp (mu := volume) ⊤ χ) u x = _
  rw [hx, hχ]
  rfl

/-- Theorem 3.1, localized flux limits: the continuous bilinear form
is the integral of the physical stress, displacement and cutoff gradient. -/
theorem cutoffPairing_eq_integral (χ : 𝓓(Ω, ℝ))
    (σ : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (u : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    cutoffPairing χ σ u = ∫ x in (Ω : Set (PhysicalSpace d)),
      ∑ ij : Fin d × Fin d, (σ x).val ij * u x ij.1 *
        (∇ (χ : PhysicalSpace d → ℝ) x) ij.2 := by
  change ⟪(symmetricSubmodule d).subtypeL.compLpL 2
    (volume.restrict (Ω : Set (PhysicalSpace d))) σ, cutoffGradientL χ u⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(symmetricSubmodule d).subtypeL.coeFn_compLpL σ,
    cutoffGradientL_apply_ae χ u] with x hσ hu
  rw [hσ, hu]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro ij _
  change (u x ij.1 * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2) * (σ x).val ij = _
  ring

/-- Theorem 3.1, localized weak tests: the full-gradient product rule
splits the stress pairing into the localized strain and cutoff terms. -/
theorem integral_stress_cutoff_gradient (χ : 𝓓(Ω, ℝ))
    (σ : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (u : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (G : Lp (SecondOrder d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (v : VectorH1 Ω)
    (hv : VectorH1.gradientL Ω v =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      WithLp.toLp 2 (fun ij => χ x * G x ij +
        u x ij.1 * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2)) :
    (∫ x in (Ω : Set (PhysicalSpace d)), ⟪σ x, VectorH1.symmetricGradientL Ω v x⟫_ℝ) =
      (∫ x in (Ω : Set (PhysicalSpace d)), χ x * ⟪(σ x).val, G x⟫_ℝ) +
        cutoffPairing χ σ u := by
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  let sigmaFull := (symmetricSubmodule d).subtypeL.compLpL 2 μ σ
  let a := TauCeti.testFunctionLp (mu := volume) ⊤ χ
  let M := (ContinuousLinearMap.lsmul ℝ ℝ (E := SecondOrder d)).holder 2 a G
  have hsigmaFull : sigmaFull =ᵐ[μ] fun x => (σ x).val :=
    (symmetricSubmodule d).subtypeL.coeFn_compLpL σ
  have hM : M =ᵐ[μ] fun x => χ x • G x := by
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := SecondOrder d)).coeFn_holder
      (r := 2) a G, TauCeti.testFunctionLp_apply_ae (mu := volume) ⊤ χ] with x hx hχ
    rw [hx]
    change a x • G x = _
    rw [hχ]
  have hgrad : VectorH1.gradientL Ω v = M + cutoffGradientL χ u := by
    apply Lp.ext
    filter_upwards [hv, hM, cutoffGradientL_apply_ae χ u,
      Lp.coeFn_add M (cutoffGradientL χ u)] with x hx hmx hux hadd
    rw [hx, hadd, Pi.add_apply, hmx, hux]
    apply PiLp.ext
    intro ij
    rfl
  have hstrain :
      (∫ x in (Ω : Set (PhysicalSpace d)), ⟪σ x, VectorH1.symmetricGradientL Ω v x⟫_ℝ) =
        ⟪sigmaFull, VectorH1.gradientL Ω v⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(symmetrizeL d).coeFn_compLpL (VectorH1.gradientL Ω v), hsigmaFull]
      with x hs hx
    change ⟪σ x, (symmetrizeL d).compLpL 2 μ (VectorH1.gradientL Ω v) x⟫_ℝ = _
    rw [hs, hx]
    exact inner_symmetrize (σ x) (VectorH1.gradientL Ω v x)
  have hmain : ⟪sigmaFull, M⟫_ℝ =
      ∫ x in (Ω : Set (PhysicalSpace d)), χ x * ⟪(σ x).val, G x⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hsigmaFull, hM] with x hs hm
    rw [hs, hm, real_inner_smul_right]
  rw [hstrain, hgrad, inner_add_right, hmain]
  rfl

/-- Theorem 3.1, localized divergence-free stresses: testing with χu
expresses the strain pairing using only the displacement value. -/
theorem integral_cutoff_stress_strain_eq_neg_pairing (χ : 𝓓(Ω, ℝ))
    (σ : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (hσ : ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)), ⟪σ x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = 0)
    (u : ZeroBoundaryH1 Ω) :
    (∫ x in (Ω : Set (PhysicalSpace d)),
      χ x * ⟪σ x, VectorH1.symmetricGradientL Ω u.val x⟫_ℝ) =
        -cutoffPairing χ σ (VectorH1.valueL Ω u.val) := by
  obtain ⟨v, _, hv⟩ := ZeroBoundaryH1.exists_cutoff χ u
  have h := integral_stress_cutoff_gradient χ σ (VectorH1.valueL Ω u.val)
    (VectorH1.gradientL Ω u.val) v.val hv
  rw [hσ v] at h
  have heq :
      (∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * ⟪σ x, VectorH1.symmetricGradientL Ω u.val x⟫_ℝ) =
      ∫ x in (Ω : Set (PhysicalSpace d)),
        χ x * ⟪(σ x).val, VectorH1.gradientL Ω u.val x⟫_ℝ := by
    apply integral_congr_ae
    filter_upwards [(symmetrizeL d).coeFn_compLpL (VectorH1.gradientL Ω u.val)] with x hx
    change χ x * ⟪σ x, (symmetrizeL d).compLpL 2
      (volume.restrict (Ω : Set (PhysicalSpace d))) (VectorH1.gradientL Ω u.val) x⟫_ℝ = _
    rw [hx]
    rw [show symmetrizeL d (VectorH1.gradientL Ω u.val x) =
      symmetrize (VectorH1.gradientL Ω u.val x) from rfl, inner_symmetrize]
  rw [heq]
  linarith

end KVApproximation.Analysis
