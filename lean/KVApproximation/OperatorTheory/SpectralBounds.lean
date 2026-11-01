module

public import KVApproximation.OperatorTheory.WeightedRelaxation
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus

/-!
# The relaxation spectrum in the original and weighted norms

The energy bounds of Appendix A.2 give operator inequalities in the viscous
Hilbert space. Continuous conjugation and complexification then preserve the
spectral interval needed for the memory measure.
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.2: changing to the equivalent viscous Hilbert norm preserves the spectrum. -/
theorem weightedRelaxation_spectrum_eq (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) :
    spectrum ℝ (weightedRelaxation V E X) = spectrum ℝ (relaxation V E X) := by
  let e := (WeightedSpace.continuousLinearEquiv (V.restrict X)).symm
  change spectrum ℝ (e.conjContinuousAlgEquiv (relaxation V E X)) = _
  exact AlgEquiv.spectrum_eq e.conjContinuousAlgEquiv.toAlgEquiv _

/-- Section 3.2: only the elastic lower and viscous upper bounds are needed
for the lower relaxation bound. -/
theorem weightedRelaxation_lower_bound (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) {αV βV αE βE : ℝ} (hβV : 0 < βV) (hαE : 0 < αE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    algebraMap ℝ _ (αE / βV) ≤ weightedRelaxation V E X := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
  refine ⟨(weightedRelaxation_isSelfAdjoint V E X).sub
    (IsSelfAdjoint.algebraMap _ (.all _)), fun u => ?_⟩
  have halg (r : ℝ) (w : RelaxationSpace V X) :
      algebraMap ℝ (RelaxationSpace V X →L[ℝ] RelaxationSpace V X) r w = r • w := rfl
  simp only [sub_apply, inner_sub_left, halg]
  rw [real_inner_smul_left u u (αE / βV)]
  -- In the transported coordinates, the inner product is the viscous form.
  change 0 ≤ V.form (relaxation V E X u.val) u.val - αE / βV * V.form u.val u.val
  apply sub_nonneg.mpr
  rw [relaxation_spec]
  calc
    αE / βV * V.form u.val u.val ≤ αE / βV * (βV * ‖(u.val : H)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hV u.val).2 (div_nonneg hαE.le hβV.le)
    _ = αE * ‖(u.val : H)‖ ^ 2 := by rw [← mul_assoc, div_mul_cancel₀ _ hβV.ne']
    _ ≤ E.form u.val u.val := (hE u.val).1

/-- Appendix A.2: Rayleigh bounds are order bounds in the viscous inner product. -/
private theorem weightedRelaxation_order_bounds (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    algebraMap ℝ _ (αE / βV) ≤ weightedRelaxation V E X ∧
      weightedRelaxation V E X ≤ algebraMap ℝ _ (βE / αV) := by
  have hR := weightedRelaxation_isSelfAdjoint V E X
  have halg (r : ℝ) (u : RelaxationSpace V X) :
      algebraMap ℝ (RelaxationSpace V X →L[ℝ] RelaxationSpace V X) r u = r • u := rfl
  constructor
  · exact weightedRelaxation_lower_bound V E X hβV hαE hV hE
  · rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
    refine ⟨(IsSelfAdjoint.algebraMap _ (.all _)).sub hR, fun u => ?_⟩
    simp only [sub_apply, inner_sub_left, halg]
    rw [real_inner_smul_left u u (βE / αV)]
    -- Use the same underlying vectors in the restricted viscous form.
    change 0 ≤ βE / αV * V.form u.val u.val - V.form (relaxation V E X u.val) u.val
    exact sub_nonneg.mpr (relaxation_energy_bounds V E X hαV hβV hαE hβE hV hE u.val).2

/-- Appendix A.2: the real spectrum of relaxation lies in the common positive interval. -/
theorem relaxation_spectrum_subset (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    spectrum ℝ (relaxation V E X) ⊆ Set.Icc (αE / βV) (βE / αV) := by
  rw [← weightedRelaxation_spectrum_eq]
  have hb := weightedRelaxation_order_bounds V E X hαV hβV hαE hβE hV hE
  have hR := weightedRelaxation_isSelfAdjoint V E X
  intro r hr
  exact ⟨(algebraMap_le_iff_le_spectrum hR).mp hb.1 r hr,
    (le_algebraMap_iff_spectrum_le hR).mp hb.2 r hr⟩

/-- Appendix A.2: complexification preserves the common spectral interval. -/
theorem weightedRelaxation_complex_spectrum_subset (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) {αV βV αE βE : ℝ}
    (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    ∀ z ∈ spectrum ℂ (weightedRelaxation V E X).complexifyL2,
      z.re ∈ Set.Icc (αE / βV) (βE / αV) := by
  have hR := weightedRelaxation_isSelfAdjoint V E X
  have hC : IsSelfAdjoint (weightedRelaxation V E X).complexifyL2 := by simpa using hR
  intro z hz
  have hzreal := hC.spectrumRestricts.apply_mem hz
  rw [ContinuousLinearMap.spectrum_complexifyL2 hR, weightedRelaxation_spectrum_eq] at hzreal
  exact relaxation_spectrum_subset V E X hαV hβV hαE hβE hV hE hzreal

end KVApproximation.OperatorTheory
