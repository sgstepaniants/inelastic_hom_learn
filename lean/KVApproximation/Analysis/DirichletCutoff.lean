module

public import KVApproximation.Analysis.SobolevCutoff
public import KVApproximation.Analysis.VectorSobolevProperties
public import KVApproximation.Analysis.ZeroBoundaryCoordinates

/-!
# Cutoffs of Dirichlet displacements

Scalar Sobolev cutoff multiplication assembles componentwise into the
physical displacement and full-gradient fields.
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions Gradient

namespace KVApproximation.Analysis

private theorem scalarCutoff_ae {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (χ : 𝓓(Ω, ℝ)) (u v : TauCeti.W1p volume Ω 2)
    (h : (v : TauCeti.Sobolev1JetLp volume Ω 2) =
      cutoffJetL χ (u : TauCeti.Sobolev1JetLp volume Ω 2)) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      TauCeti.W1p.value v x = χ x * TauCeti.W1p.value u x ∧
      TauCeti.W1p.gradient v x = χ x • TauCeti.W1p.gradient u x +
        TauCeti.W1p.value u x • ∇ (χ : PhysicalSpace d → ℝ) x := by
  filter_upwards [TauCeti.W1p.value_apply_ae v, TauCeti.W1p.gradient_apply_ae v,
    cutoffJetL_apply_ae χ (u : TauCeti.Sobolev1JetLp volume Ω 2),
    TauCeti.W1p.value_apply_ae u, TauCeti.W1p.gradient_apply_ae u]
    with x hv hg hc hu hgu
  constructor
  · rw [hv, h, hc, hu]
    rfl
  · rw [hg, h, hc, hu, hgu]
    rfl

/-- Theorem 3.1, localized static tests: multiplication by a smooth
compactly supported scalar preserves the vector Dirichlet space and
has the full gradient product rule in physical coordinates. -/
theorem ZeroBoundaryH1.exists_cutoff {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (χ : 𝓓(Ω, ℝ)) (u : ZeroBoundaryH1 Ω) :
    ∃ v : ZeroBoundaryH1 Ω,
      (VectorH1.valueL Ω v.val =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => χ x • VectorH1.valueL Ω u.val x) ∧
      (VectorH1.gradientL Ω v.val =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => WithLp.toLp 2 (fun ij => χ x * VectorH1.gradientL Ω u.val x ij +
          VectorH1.valueL Ω u.val x ij.1 * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2)) := by
  have hex (i : Fin d) := cutoffJetL_mem_of_zeroBoundary χ (u.val i)
    ((mem_zeroBoundary_iff u.val).mp u.property i)
  choose w hw heq using hex
  let v : VectorH1 Ω := WithLp.toLp 2 w
  have hv : v ∈ zeroBoundarySubmodule Ω := (mem_zeroBoundary_iff v).mpr hw
  have hcomp (i : Fin d) := scalarCutoff_ae χ (u.val i) (w i) (heq i)
  refine ⟨⟨v, hv⟩, ?_, ?_⟩
  · filter_upwards [VectorH1.valueL_apply_ae v, VectorH1.valueL_apply_ae u.val,
      ae_all_iff.mpr hcomp] with x hvx hux hi
    rw [hvx, hux]
    apply PiLp.ext
    intro i
    exact (hi i).1
  · filter_upwards [VectorH1.gradientL_apply_ae v, VectorH1.gradientL_apply_ae u.val,
      VectorH1.valueL_apply_ae u.val, ae_all_iff.mpr hcomp] with x hvx hgx hux hi
    rw [hvx, hgx, hux]
    apply PiLp.ext
    intro ij
    change (TauCeti.W1p.gradient (w ij.1) x) ij.2 =
      χ x * (TauCeti.W1p.gradient (u.val ij.1) x) ij.2 +
        TauCeti.W1p.value (u.val ij.1) x * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
      congrArg (fun z : PhysicalSpace d => z ij.2) (hi ij.1).2

end KVApproximation.Analysis
