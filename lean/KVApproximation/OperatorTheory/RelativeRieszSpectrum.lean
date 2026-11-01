module

public import KVApproximation.OperatorTheory.CoerciveSolverProperties
public import KVApproximation.OperatorTheory.SpectralBounds

/-!
# Spectrum of the full-space relative Riesz operator
-/

public section

noncomputable section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Remark 1.2 (`rem:2`), relaxation rates: the full-space relative
Riesz operator has the same positive spectral bounds as its variational
realization, with the spectrum taken in the original Hilbert norm. -/
theorem relativeRiesz_spectrum_subset (V E : CoerciveForm H)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) :
    spectrum ℝ (relativeRiesz V E) ⊆ Set.Icc (αE / βV) (βE / αV) := by
  let e : (⊤ : ClosedSubmodule ℝ H) ≃L[ℝ] H := {
    toLinearEquiv := {
      toFun := fun u => u.val
      invFun := fun u => ⟨u, by trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    continuous_toFun := continuous_subtype_val
    continuous_invFun := continuous_id.subtype_mk (fun _ => by trivial) }
  have he : e.conjContinuousAlgEquiv (relaxation V E ⊤) = relativeRiesz V E := by
    apply ContinuousLinearMap.ext
    intro u
    apply V.eq_of_form_eq
    intro v
    change V.form (relaxation V E ⊤ ⟨u, by trivial⟩ : H) v =
      V.form (relativeRiesz V E u) v
    exact (relaxation_spec V E ⊤ ⟨u, by trivial⟩ ⟨v, by trivial⟩).trans
      (relativeRiesz_spec V E u v).symm
  have hs : spectrum ℝ (relativeRiesz V E) = spectrum ℝ (relaxation V E ⊤) := by
    rw [← he]
    exact AlgEquiv.spectrum_eq e.conjContinuousAlgEquiv.toAlgEquiv _
  rw [hs]
  exact relaxation_spectrum_subset V E ⊤ hαV hβV hαE hβE hV hE

end KVApproximation.OperatorTheory
