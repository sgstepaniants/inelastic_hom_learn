module

public import KVApproximation.Homogenization.CorrectorSpace
public import KVApproximation.Analysis.PeriodicBump
public import KVApproximation.Analysis.PeriodicNonconstantStrain

/-!
# Strain correctors supported in coordinate strips
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Proposition 4.7, normalization: mean removal preserves the localized
strain, which can be scaled to unit L² norm without changing its support. -/
private theorem unit_strain_of_nonconstant
    {d : ℕ} (φ : PeriodicC1 d (EuclideanSpace ℝ (Fin d)))
    (hnonconstant : ∃ y z, φ.value y ≠ φ.value z)
    (S : Set (PeriodicCell d)) (hsupport : tsupport φ.value ⊆ S) :
    ∃ u : ZeroMeanPeriodicH1 d,
      ‖correctorGradientL d u‖ = 1 ∧
      ∀ᵐ y ∂cellMeasure d, y ∉ S → correctorGradientL d u y = 0 := by
  obtain ⟨v, _, hstrain, hne⟩ := φ.exists_zeroMean_nonzero_strain hnonconstant
  have hlocal : ∀ᵐ y ∂cellMeasure d, y ∉ S → correctorGradientL d v y = 0 := by
    filter_upwards [hstrain] with y hy
    intro hout
    have hnot : y ∉ tsupport φ.value := fun h => hout (hsupport h)
    have hgrad : periodicGradient φ.value y = 0 := by
      ext ij
      change φ.partial ij.2 y ij.1 = 0
      rw [φ.partial_eq_zero_of_notMem_tsupport ij.2 hnot]
      rfl
    rw [hy, hgrad, map_zero]
  let u : ZeroMeanPeriodicH1 d := ‖correctorGradientL d v‖⁻¹ • v
  have hu : correctorGradientL d u =
      ‖correctorGradientL d v‖⁻¹ • correctorGradientL d v :=
    (correctorGradientL d).map_smul _ v
  refine ⟨u, ?_, ?_⟩
  · rw [hu]
    exact norm_smul_inv_norm (𝕜 := ℝ) (E := StrainField d) hne
  · rw [hu]
    filter_upwards [hlocal, Lp.coeFn_smul ‖correctorGradientL d v‖⁻¹
      (correctorGradientL d v)] with y hy hsmul
    intro hout
    exact hsmul.trans (by
      change ‖correctorGradientL d v‖⁻¹ • correctorGradientL d v y = 0
      rw [hy hout, smul_zero])

/-- Proposition 4.7 (`prop:no_spectral_stability`), localized correctors:
each positive-width coordinate strip contains a unit strain corrector
arising from an actual zero-mean periodic displacement. -/
theorem exists_unit_corrector_in_coordinate_strip {d : ℕ} (i : Fin d)
    {a : ℝ} (ha : 0 < a) (ha_one : a ≤ 1) :
    ∃ u : ZeroMeanPeriodicH1 d,
      ∃ η : (correctorSubspace d).toSubmodule,
        (η : StrainField d) = correctorGradientL d u ∧
        ‖η‖ = 1 ∧
        ∀ᵐ y ∂cellMeasure d,
          y ∉ {y : PeriodicCell d |
            0 < cellRepresentative y i ∧ cellRepresentative y i < a} →
            (η : StrainField d) y = 0 := by
  classical
  obtain ⟨ψ, hψsmooth, _, hψsupport, yc, hyc⟩ := exists_periodic_strip_bump i ha ha_one
  let e : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single i (1 : ℝ))
  have hei : e i = 1 := by
    change (Pi.single i (1 : ℝ) : Fin d → ℝ) i = 1
    simp only [Pi.single_eq_same]
  let φ : PeriodicC1 d (EuclideanSpace ℝ (Fin d)) :=
    ⟨fun y => ψ.value y • e, (hψsmooth.smul contDiff_const).of_le (by simp)⟩
  let S : Set (PeriodicCell d) :=
    {y | 0 < cellRepresentative y i ∧ cellRepresentative y i < a}
  have hφsupport : tsupport φ.value ⊆ S :=
    (tsupport_smul_subset_left ψ.value (fun _ => e)).trans hψsupport
  let y₀ : PeriodicCell d := toCell e
  have hy₀ : cellRepresentative y₀ i = 1 := by
    change (AddCircle.equivIoc (1 : ℝ) 0 ((e i : ℝ) : UnitAddCircle)).val = 1
    rw [hei]
    exact AddCircle.equivIoc_coe_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ioc 0 (0 + 1))
  have hout : y₀ ∉ S := by
    intro h
    have hlt : cellRepresentative y₀ i < a := h.2
    rw [hy₀] at hlt
    exact (not_lt_of_ge ha_one) hlt
  have hzero : ψ.value y₀ = 0 := by
    by_contra hne
    exact hout (hψsupport (subset_closure hne))
  have hnonconstant : ∃ y z, φ.value y ≠ φ.value z := by
    refine ⟨yc, y₀, ?_⟩
    intro heq
    have hi := congrArg (fun w : EuclideanSpace ℝ (Fin d) => w i) heq
    change ψ.value yc * e i = ψ.value y₀ * e i at hi
    rw [hyc, hzero, hei] at hi
    norm_num at hi
  obtain ⟨u, hnorm, hlocal⟩ := unit_strain_of_nonconstant φ hnonconstant S hφsupport
  have hmem : correctorGradientL d u ∈ correctorSubspace d :=
    (LinearMap.range (correctorGradientL d).toLinearMap).le_topologicalClosure ⟨u, rfl⟩
  exact ⟨u, ⟨correctorGradientL d u, hmem⟩, rfl, hnorm, hlocal⟩

end KVApproximation.Homogenization
