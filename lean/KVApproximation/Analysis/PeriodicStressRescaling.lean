module

public import KVApproximation.Analysis.PeriodicDivergenceRescaling
public import KVApproximation.Analysis.PeriodicSmoothSobolev
public import KVApproximation.Analysis.VectorSobolevProperties
public import KVApproximation.Analysis.ZeroBoundaryCoordinates

/-!
# Divergence-free periodic stresses in physical space

Symmetric-gradient orthogonality gives scalar zero divergence for each
stress row. Rescaling these row identities and recombining the Frobenius
pairing gives every physical Dirichlet test.
-/

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Analysis

private noncomputable def stressRowL {d : ℕ} (i : Fin d) :
    Symmetric d →L[ℝ] PhysicalSpace d :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => PhysicalSpace d) i).comp
    ((gradientRowCoordinates d).symm.toContinuousLinearMap.comp
      (symmetricSubmodule d).subtypeL)

private theorem stressRowL_apply {d : ℕ} (i : Fin d) (s : Symmetric d) :
    stressRowL i s = WithLp.toLp 2 (fun j => s.val (i, j)) := rfl

private theorem stressRow_zeroDivergence {d : ℕ}
    (σ : Lp (Symmetric d) 2 (cellMeasure d))
    (hσ : ∀ w : PeriodicH1 d, ⟪σ, PeriodicH1.symmetricGradientL d w⟫_ℝ = 0)
    (i : Fin d) :
    HasPeriodicZeroDivergence ((stressRowL i).compLpL 2 (cellMeasure d) σ) := by
  classical
  intro φ
  let ψ : PeriodicC1 d (PhysicalSpace d) :=
    ⟨fun y => φ.value y • EuclideanSpace.single i 1,
      φ.contDiff_lift.smul contDiff_const⟩
  obtain ⟨u, _, hg⟩ := ψ.exists_periodicH1
  have hsg : PeriodicH1.symmetricGradientL d u =ᵐ[cellMeasure d]
      fun y => symmetrize (PeriodicH1.gradientL d u y) :=
    (symmetrizeL d).coeFn_compLpL (PeriodicH1.gradientL d u)
  have hG (y : PeriodicCell d) (k j : Fin d) :
      periodicGradient ψ.value y (k, j) = if k = i then φ.partial j y else 0 := by
    have hd := (φ.contDiff_lift.differentiable one_ne_zero
      (cellRepresentative y)).hasFDerivAt.smul_const (EuclideanSpace.single i (1 : ℝ))
    change (fderiv ℝ (fun x : PhysicalSpace d =>
      φ.value (toCell x) • EuclideanSpace.single i 1) (cellRepresentative y)
        (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) k = _
    rw [hd.fderiv]
    change (φ.partial j y • EuclideanSpace.single i (1 : ℝ)) k = _
    simp [PiLp.smul_apply, PiLp.single_apply, eq_comm]
  have heq : ⟪σ, PeriodicH1.symmetricGradientL d u⟫_ℝ =
      ∫ y, ∑ j, ((stressRowL i).compLpL 2 (cellMeasure d) σ) y j *
        φ.partial j y ∂cellMeasure d := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hsg, hg, (stressRowL i).coeFn_compLpL σ] with y hs hy hr
    rw [hs, hy, inner_symmetrize, hr, stressRowL_apply]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    change (∑ ij, periodicGradient ψ.value y ij * (σ y).val ij) =
      ∑ j, (σ y).val (i, j) * φ.partial j y
    rw [Fintype.sum_prod_type]
    simp [hG, ite_mul, Finset.sum_ite_irrel, mul_comm]
  exact heq.symm.trans (hσ u)

/-- Theorem 3.1, static oscillating fluxes: a periodic symmetric stress
orthogonal to all periodic strains remains orthogonal to all physical
Dirichlet strains after rescaling. -/
theorem integral_rescale_stress_strain_eq_zero {d : ℕ}
    (σ : Lp (Symmetric d) 2 (cellMeasure d))
    (hσ : ∀ w : PeriodicH1 d, ⟪σ, PeriodicH1.symmetricGradientL d w⟫_ℝ = 0)
    {Ω : Opens (PhysicalSpace d)} (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (v : ZeroBoundaryH1 Ω) :
    (∫ x in (Ω : Set (PhysicalSpace d)),
      ⟪rescalePeriodic σ ε x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = 0 := by
  let q (i : Fin d) := (stressRowL i).compLpL 2 (cellMeasure d) σ
  have hzero (i : Fin d) :
      (∫ x in (Ω : Set (PhysicalSpace d)),
        ⟪rescalePeriodic (q i) ε x, TauCeti.W1p.gradient (v.val i) x⟫_ℝ) = 0 :=
    (stressRow_zeroDivergence σ hσ i).integral_rescale_gradient_eq_zero hΩ hε hε₁
      (v.val i) ((mem_zeroBoundary_iff v.val).mp v.property i)
  have hr (i : Fin d) : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      rescalePeriodic (q i) ε x = WithLp.toLp 2
        (fun j => (rescalePeriodic σ ε x).val (i, j)) := by
    have ha := ae_restrict_of_ae (s := (Ω : Set (PhysicalSpace d)))
      ((quasiMeasurePreserving_scaledToCell hε.ne').ae
      ((stressRowL i).coeFn_compLpL σ))
    filter_upwards [ha] with x hx
    change (q i) (toCell (ε⁻¹ • x)) = _
    rw [hx, stressRowL_apply]
    rfl
  have heq : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      ⟪rescalePeriodic σ ε x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ =
        ∑ i, ⟪rescalePeriodic (q i) ε x, TauCeti.W1p.gradient (v.val i) x⟫_ℝ := by
    filter_upwards [VectorH1.symmetricGradientL_apply_ae v.val, ae_all_iff.mpr hr]
      with x hs hx
    rw [hs]
    change ⟪rescalePeriodic σ ε x, symmetrize (VectorH1.gradient v.val x)⟫_ℝ = _
    rw [inner_symmetrize]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    change (∑ ij, (TauCeti.W1p.gradient (v.val ij.1) x) ij.2 *
      (rescalePeriodic σ ε x).val ij) =
      ∑ i, ∑ j, (TauCeti.W1p.gradient (v.val i) x) j * (rescalePeriodic (q i) ε x) j
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i]
  have hi (i : Fin d) : Integrable (fun x =>
      ⟪rescalePeriodic (q i) ε x, TauCeti.W1p.gradient (v.val i) x⟫_ℝ)
      (volume.restrict (Ω : Set (PhysicalSpace d))) := by
    have hm := memLp_two_rescalePeriodic hΩ hε hε₁ (Lp.memLp (q i))
    apply (L2.integrable_inner (𝕜 := ℝ) (hm.toLp (rescalePeriodic (q i) ε))
      (TauCeti.W1p.gradient (v.val i))).congr
    filter_upwards [hm.coeFn_toLp] with x hx
    rw [hx]
  rw [integral_congr_ae heq, integral_finsetSum _ (fun i _ => hi i)]
  simp only [hzero, Finset.sum_const_zero]

end KVApproximation.Analysis
