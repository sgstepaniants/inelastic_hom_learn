module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Support and continuous integration for the bounded spectral measure

The diagonal measure is the pushforward of the continuous functional calculus
measure from the complex spectrum to its real coordinate. This gives the
interval support and spectral integration used in Appendix A.2 and Lemma B.5.
-/

public section

open MeasureTheory TauCeti.BorelCalculus
open scoped InnerProductSpace

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Appendix A.2: the real coordinate embeds the self-adjoint spectrum,
including for the zero Hilbert space. -/
private theorem reCoord_closedEmbedding {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) :
    Topology.IsClosedEmbedding (reCoord (T := R)) := by
  have hc : Continuous (reCoord (T := R)) := by
    change Continuous (fun z : spectrum ℂ R => reCoord z)
    simp_rw [reCoord_apply]
    exact Complex.continuous_re.comp continuous_subtype_val
  apply hc.isClosedEmbedding
  intro z w h
  simp only [reCoord_apply] at h
  apply Subtype.ext
  calc
    (z : ℂ) = ((z : ℂ).re : ℂ) := (hR.spectrumRestricts.rightInvOn z.property).symm
    _ = ((w : ℂ).re : ℂ) := congrArg Complex.ofReal h
    _ = w := hR.spectrumRestricts.rightInvOn w.property

/-- Appendix A.2: a common spectral interval supports the canonical bounded PVM. -/
theorem boundedPVM_supported {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) {a b : ℝ}
    (hI : ∀ z ∈ spectrum ℂ R, z.re ∈ Set.Icc a b) :
    (boundedPVM hR).proj (Set.Icc a b) measurableSet_Icc =
        ContinuousLinearMap.id ℂ H ∧
      (boundedPVM hR).proj (Set.Icc a b)ᶜ measurableSet_Icc.compl = 0 := by
  have hfull : (boundedPVM hR).proj (Set.Icc a b) measurableSet_Icc =
      ContinuousLinearMap.id ℂ H := by
    rw [boundedPVM_proj_eq_cfcHom hR _ measurableSet_Icc (1 : C(spectrum ℂ R, ℂ))
      (fun z => by simp [reCoord_apply, hI z z.property])]
    exact map_one (cfcHom hR.isStarNormal)
  refine ⟨hfull, ?_⟩
  rw [(boundedPVM hR).proj_compl _ measurableSet_Icc, hfull, sub_self]

/-- Appendix A.2 and Lemma B.5: continuous spectral tests agree with the
functional calculus through the finite scalar diagonal measures. -/
theorem boundedPVM_integral {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) {a b : ℝ}
    (hI : ∀ z ∈ spectrum ℂ R, z.re ∈ Set.Icc a b)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (u : H) :
    Integrable f ((boundedPVM hR).diag u) ∧
      (∫ r, f r ∂(boundedPVM hR).diag u) = (⟪u, cfc f R u⟫_ℂ).re := by
  have hc : Continuous (fun z : spectrum ℂ R => f (reCoord z)) := by
    simp only [reCoord_apply]
    exact hf.comp_continuous (Complex.continuous_re.comp continuous_subtype_val)
      (fun z => hI z z.property)
  let g : C(spectrum ℂ R, ℝ) := ⟨fun z => f (reCoord z), hc⟩
  have hi : Integrable g (diagMeasure hR.isStarNormal u) :=
    integrable_of_continuous hR.isStarNormal u g
  have hcalculus : cfc f R = cfcHom hR.isStarNormal (ofRealLM g) := by
    have hfc : ContinuousOn (fun z : ℂ => (f z.re : ℂ)) (spectrum ℂ R) :=
      Complex.continuous_ofReal.comp_continuousOn
        (hf.comp Complex.continuous_re.continuousOn hI)
    rw [cfc_real_eq_complex f hR, cfc_apply _ R hR.isStarNormal hfc]
    congr 1
    ext z
    simp [g, reCoord_apply]
  rw [boundedPVM_diag]
  constructor
  · exact (reCoord_closedEmbedding hR).measurableEmbedding.integrable_map_iff.mpr hi
  · rw [(reCoord_closedEmbedding hR).integral_map, hcalculus]
    exact integral_diagMeasure_ofReal hR.isStarNormal u g

end KVApproximation.Spectral
