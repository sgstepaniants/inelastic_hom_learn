module

public import KVApproximation.Analysis.PeriodicRescaledJetProperties
public import KVApproximation.Analysis.PeriodicRescalingLp
public import KVApproximation.Analysis.SobolevCutoff
public import KVApproximation.Analysis.VectorSobolevProperties
public import KVApproximation.Analysis.ZeroBoundaryCoordinates

/-!
# Localized periodic correctors

Smooth cutoff multiplication puts rescaled periodic jets into the actual
Dirichlet space. Closedness extends the construction from smooth periodic
generators to every periodic H¹ displacement.
-/

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped Distributions Gradient ENNReal

namespace KVApproximation.Analysis

open PeriodicRescaledJets

/-- Theorem 3.1, oscillating static tests: a scalar compactly supported
cutoff of the scaled periodic corrector is an actual Dirichlet displacement,
with the full weak-gradient product rule. -/
theorem PeriodicH1.exists_rescaled_cutoff {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (χ : 𝓓(Ω, ℝ)) (u : PeriodicH1 d) :
    ∃ v : ZeroBoundaryH1 Ω,
      (VectorH1.valueL Ω v.val =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => χ x • (ε • rescalePeriodic (PeriodicH1.valueL d u) ε x)) ∧
      (VectorH1.gradientL Ω v.val =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => WithLp.toLp 2 (fun ij =>
          χ x * rescalePeriodic (PeriodicH1.gradientL d u) ε x ij +
          (ε * rescalePeriodic (PeriodicH1.valueL d u) ε x ij.1) *
            (∇ (χ : PhysicalSpace d → ℝ) x) ij.2)) := by
  obtain ⟨C, _, hbound⟩ := exists_rescaling_measure_bound hΩ
  have hq := (quasiMeasurePreserving_scaledToCell (d := d) hε.ne').measurable
  let R := rescaleJet hq ENNReal.ofReal_ne_top (hbound ε hε hε₁)
  let T (i : Fin d) : PeriodicJetField d →L[ℝ] TauCeti.Sobolev1JetLp volume Ω 2 :=
    ((jetCoordinate ε i).compLpL 2 (volume.restrict (Ω : Set (PhysicalSpace d)))).comp R
  have hT (i : Fin d) (w : PeriodicJetField d) :
      ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
        T i w x = jetCoordinate ε i (w (toCell (ε⁻¹ • x))) := by
    filter_upwards [(jetCoordinate ε i).coeFn_compLpL (R w),
      rescaleJet_ae hq ENNReal.ofReal_ne_top (hbound ε hε hε₁) w] with x ht hr
    change ((jetCoordinate ε i).compLpL 2 (volume.restrict (Ω : Set (PhysicalSpace d)))
      (R w)) x = _
    rw [ht, hr]
    rfl
  let S : Submodule ℝ (TauCeti.Sobolev1JetLp volume Ω 2) :=
    (TauCeti.w1p0Submodule volume Ω 2).toSubmodule.map
      (TauCeti.w1pSubmodule volume Ω 2).toSubmodule.subtype
  have hS : IsClosed (S : Set (TauCeti.Sobolev1JetLp volume Ω 2)) :=
    (TauCeti.w1pSubmodule volume Ω 2).isClosed.isClosedEmbedding_subtypeVal.isClosedMap _
      (TauCeti.w1p0Submodule volume Ω 2).isClosed
  let K₀ : ClosedSubmodule ℝ (TauCeti.Sobolev1JetLp volume Ω 2) := ⟨S, hS⟩
  have hmem (i : Fin d) : cutoffJetL χ (T i u.val) ∈ S := by
    let K : ClosedSubmodule ℝ (PeriodicJetField d) :=
      K₀.comap ((cutoffJetL χ).comp (T i))
    have hle : periodicH1Submodule d ≤ K := by
      apply Submodule.closure_le.mpr
      apply Submodule.span_le.mpr
      rintro w ⟨φ, hφ, hw⟩
      let ψ : PeriodicC1 d (PhysicalSpace d) := ⟨φ, hφ.of_le (by simp)⟩
      let f : PhysicalSpace d → ℝ := fun x => ε * φ (toCell (ε⁻¹ • x)) i
      have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
        contDiff_const.mul
          (((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i).contDiff.comp hφ).comp
            (ε⁻¹ • ContinuousLinearMap.id ℝ (PhysicalSpace d)).contDiff)
      have hwr : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
          w (toCell (ε⁻¹ • x)) = WithLp.toLp 2
            (φ (toCell (ε⁻¹ • x)), periodicGradient φ (toCell (ε⁻¹ • x))) :=
        ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hε.ne').ae hw)
      change cutoffJetL χ (T i w) ∈ S
      apply cutoffJetL_mem_of_smooth χ (T i w) hf
      · filter_upwards [TauCeti.Sobolev1JetLp.value_apply_ae (T i w), hT i w, hwr]
          with x ht hj hwx
        rw [ht, hj, hwx, jetCoordinate_apply]
        rfl
      · filter_upwards [TauCeti.Sobolev1JetLp.gradient_apply_ae (T i w), hT i w, hwr]
          with x ht hj hwx
        rw [ht, hj, hwx, jetCoordinate_apply]
        exact (gradient_scaled_component ψ hε.ne' i x).symm
    exact hle u.property
  have hex (i : Fin d) : ∃ w : TauCeti.W1p volume Ω 2,
      w ∈ TauCeti.w1p0Submodule volume Ω 2 ∧
      (w : TauCeti.Sobolev1JetLp volume Ω 2) = cutoffJetL χ (T i u.val) := hmem i
  choose w hw heq using hex
  let v : VectorH1 Ω := WithLp.toLp 2 w
  have hv : v ∈ zeroBoundarySubmodule Ω := (mem_zeroBoundary_iff v).mpr hw
  have hval : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      PeriodicH1.valueL d u (toCell (ε⁻¹ • x)) = WithLp.fst (u.val (toCell (ε⁻¹ • x))) :=
    ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hε.ne').ae
      ((WithLp.fstL 2 ℝ (PhysicalSpace d) (SecondOrder d)).coeFn_compLpL u.val))
  have hgrad : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      PeriodicH1.gradientL d u (toCell (ε⁻¹ • x)) = WithLp.snd (u.val (toCell (ε⁻¹ • x))) :=
    ae_restrict_of_ae ((quasiMeasurePreserving_scaledToCell hε.ne').ae
      ((WithLp.sndL 2 ℝ (PhysicalSpace d) (SecondOrder d)).coeFn_compLpL u.val))
  have hcomp (i : Fin d) : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      TauCeti.W1p.value (w i) x =
        χ x * (ε * PeriodicH1.valueL d u (toCell (ε⁻¹ • x)) i) ∧
      TauCeti.W1p.gradient (w i) x =
        χ x • WithLp.toLp 2 (fun j =>
          PeriodicH1.gradientL d u (toCell (ε⁻¹ • x)) (i, j)) +
        (ε * PeriodicH1.valueL d u (toCell (ε⁻¹ • x)) i) •
          ∇ (χ : PhysicalSpace d → ℝ) x := by
    filter_upwards [TauCeti.W1p.value_apply_ae (w i),
      TauCeti.W1p.gradient_apply_ae (w i), cutoffJetL_apply_ae χ (T i u.val),
      hT i u.val, hval, hgrad] with x hvx hgx hc ht hu hgu
    constructor
    · rw [hvx, heq i, hc, ht, jetCoordinate_apply, hu]
      rfl
    · rw [hgx, heq i, hc, ht, jetCoordinate_apply, hu, hgu]
      rfl
  refine ⟨⟨v, hv⟩, ?_, ?_⟩
  · filter_upwards [VectorH1.valueL_apply_ae v, ae_all_iff.mpr hcomp] with x hvx hi
    rw [hvx]
    apply PiLp.ext
    intro i
    exact (hi i).1
  · filter_upwards [VectorH1.gradientL_apply_ae v, ae_all_iff.mpr hcomp] with x hvx hi
    rw [hvx]
    apply PiLp.ext
    intro ij
    change (TauCeti.W1p.gradient (w ij.1) x) ij.2 =
      χ x * PeriodicH1.gradientL d u (toCell (ε⁻¹ • x)) ij +
      (ε * PeriodicH1.valueL d u (toCell (ε⁻¹ • x)) ij.1) *
        (∇ (χ : PhysicalSpace d → ℝ) x) ij.2
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
      congrArg (fun z : PhysicalSpace d => z ij.2) (hi ij.1).2

end KVApproximation.Analysis
