module

public import KVApproximation.KelvinVoigt.SpectralEdge
public import KVApproximation.Homogenization.LocalizedCorrectors
public import KVApproximation.Homogenization.CellRelaxationIdentities
public import KVApproximation.OperatorTheory.SpectralBounds
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Spectral edges of the identity and thin-strip materials
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Homogenization

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7, limit spectrum: a unit vector excludes the zero
space, so the identity operator has upper spectral edge one. -/
private theorem edge_one_of_eq_id
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (R : H →L[ℝ] H) (hR : R = ContinuousLinearMap.id ℝ H)
    (x : H) (hx : ‖x‖ = 1) : OperatorTheory.upperSpectralEdge R = 1 := by
  have hne : x ≠ 0 := (norm_ne_zero_iff (E := H) (a := x)).mp (by rw [hx]; norm_num)
  let : Nontrivial H := nontrivial_of_ne x 0 hne
  unfold OperatorTheory.upperSpectralEdge
  rw [hR]
  change sSup (spectrum ℝ (1 : H →L[ℝ] H)) = 1
  rw [spectrum.one_eq, csSup_singleton]

/-- Proposition 4.7, upper spectrum: an eigenvalue at a common spectral
upper bound is the supremum, without any compact-operator assumption. -/
private theorem edge_eq_of_unit_eigenvector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (R : H →L[ℝ] H) (rate : ℝ) (x : H) (hx : ‖x‖ = 1)
    (heigen : R x = rate • x) (hupper : ∀ r ∈ spectrum ℝ R, r ≤ rate) :
    OperatorTheory.upperSpectralEdge R = rate := by
  have hne : x ≠ 0 := (norm_ne_zero_iff (E := H) (a := x)).mp (by rw [hx]; norm_num)
  have hev : Module.End.HasEigenvector (R : Module.End ℝ H) rate x :=
    ⟨Module.End.mem_eigenspace_iff.mpr heigen, hne⟩
  have hmem : rate ∈ spectrum ℝ R := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact (Module.End.hasEigenvalue_of_hasEigenvector hev).mem_spectrum
  exact le_antisymm (csSup_le ⟨rate, hmem⟩ hupper) (le_csSup ⟨rate, hupper⟩ hmem)

/-- Proposition 4.7 (`prop:no_spectral_stability`), limit spectrum:
the actual identity material has upper spectral edge one while retaining
the admissible class's stored elasticity upper bound two. -/
theorem materialSpectralEdge_identity {d : ℕ} (i : Fin d)
    {γV γE : ℝ} (M : admissibleMaterials d 1 1 γV 1 2 γE)
    (hV : M.val.1 =ᵐ[cellMeasure d] fun _ => identityElasticity d)
    (hE : M.val.2 =ᵐ[cellMeasure d] fun _ => identityElasticity d) :
    materialSpectralEdge (by norm_num) (by norm_num) M = 1 := by
  let V := materialViscosity (show (0 : ℝ) < 1 from zero_lt_one) M
  let E := materialElasticity (show (0 : ℝ) < 1 from zero_lt_one) M
  have hVfield : V.field =ᵐ[cellMeasure d] fun _ => identityElasticity d :=
    M.property.1.coeFn_toLp.trans hV
  have hEfield : E.field =ᵐ[cellMeasure d] fun _ => identityElasticity d :=
    M.property.2.1.coeFn_toLp.trans hE
  have hfield : V.field = E.field := Lp.ext (hVfield.trans hEfield.symm)
  obtain ⟨_, η, _, hnorm, _⟩ :=
    exists_unit_corrector_in_coordinate_strip i (a := 1) zero_lt_one le_rfl
  change OperatorTheory.upperSpectralEdge (H := (correctorSubspace d).toSubmodule)
    (cellRelaxation V E) = 1
  exact edge_one_of_eq_id (cellRelaxation V E)
    (cellRelaxation_eq_id_of_field_eq V E hfield) η hnorm

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip spectrum:
the full relaxation operator for a thin-strip material has upper
spectral edge two, independently of the strip's positive width. -/
theorem materialSpectralEdge_strip {d : ℕ} (i : Fin d) (n : ℕ)
    {γV γE : ℝ} (M : admissibleMaterials d 1 1 γV 1 2 γE)
    (hV : M.val.1 =ᵐ[cellMeasure d] fun _ => identityElasticity d)
    (hE : M.val.2 =ᵐ[cellMeasure d] stripElasticity i n) :
    materialSpectralEdge (by norm_num) (by norm_num) M = 2 := by
  classical
  let V := materialViscosity (show (0 : ℝ) < 1 from zero_lt_one) M
  let E := materialElasticity (show (0 : ℝ) < 1 from zero_lt_one) M
  have hVfield : V.field =ᵐ[cellMeasure d] fun _ => identityElasticity d :=
    M.property.1.coeFn_toLp.trans hV
  have hEfield : E.field =ᵐ[cellMeasure d] stripElasticity i n :=
    M.property.2.1.coeFn_toLp.trans hE
  have hEjump : E.field =ᵐ[cellMeasure d]
      fun y => identityElasticity d + (thinStrip i n).indicator (fun _ => identityElasticity d) y := by
    filter_upwards [hEfield] with y hy
    rw [hy]
    by_cases hmem : y ∈ thinStrip i n
    · simp only [stripElasticity, ite_eq_left hmem, add_smul, one_smul,
        Set.indicator_of_mem hmem]
    · simp only [stripElasticity, ite_eq_right hmem, add_zero, one_smul,
        Set.indicator_of_notMem hmem]
  have hpos : 0 < (n : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hwidth : 1 / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one hpos).2 (le_add_of_nonneg_left (Nat.cast_nonneg n))
  obtain ⟨_, η, _, hnorm, hlocal⟩ :=
    exists_unit_corrector_in_coordinate_strip i (one_div_pos.mpr hpos) hwidth
  have hη : (η : StrainField d) =ᵐ[cellMeasure d]
      (thinStrip i n).indicator (fun y => (η : StrainField d) y) := by
    filter_upwards [hlocal] with y hy
    by_cases hmem : y ∈ thinStrip i n
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      exact hy hmem
  have heigen : cellRelaxation V E η = (2 : ℝ) • η := by
    calc
      cellRelaxation V E η = η + cellProjection V (η : StrainField d) :=
        cellRelaxation_eq_add_projection_of_ae_indicator V E (thinStrip i n)
          hVfield hEjump η η hη
      _ = η + η := congrArg (fun u => η + u)
        (OperatorTheory.projection_eq_self V.toForm (correctorSubspace d) η)
      _ = (2 : ℝ) • η := (two_smul ℝ η).symm
  have hVbounds : HasFieldBounds 1 1 V.field := V.bounds
  have hEbounds : HasFieldBounds 1 2 E.field := E.bounds
  have hVform : V.toForm.HasBounds 1 1 := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hVbounds u
  have hEform : E.toForm.HasBounds 1 2 := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hEbounds u
  have hspec := OperatorTheory.relaxation_spectrum_subset V.toForm E.toForm
    (correctorSubspace d) (αV := 1) (βV := 1) (αE := 1) (βE := 2)
    zero_lt_one zero_lt_one zero_lt_one (by norm_num) hVform hEform
  have hupper (r : ℝ) (hr : r ∈ spectrum ℝ (cellRelaxation V E)) : r ≤ 2 := by
    simpa only [div_one] using (hspec hr).2
  change OperatorTheory.upperSpectralEdge (H := (correctorSubspace d).toSubmodule)
    (cellRelaxation V E) = 2
  exact edge_eq_of_unit_eigenvector (cellRelaxation V E) 2 η hnorm heigen hupper

end KVApproximation.KelvinVoigt
