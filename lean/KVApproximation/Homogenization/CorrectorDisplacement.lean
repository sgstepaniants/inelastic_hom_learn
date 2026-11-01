module

public import KVApproximation.Homogenization.CorrectorRange

/-!
# Displacement recovery from a periodic strain corrector
-/

public section

open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

private noncomputable def equivOfBijective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (hinj : Function.Injective A) (hsurj : Function.Surjective A) :
    E ≃L[ℝ] F :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)

/-- Section 3.1 and Appendix A.3: a zero-mean periodic displacement is
uniquely determined by its symmetric gradient. -/
theorem correctorGradient_injective (d : ℕ) :
    Function.Injective (correctorGradientL d) := by
  intro u v huv
  have h := periodic_korn_two (d := d) (u - v)
  rw [(correctorGradientL d).map_sub u v, huv, sub_self,
    norm_zero (E := StrainField d), mul_zero] at h
  have hz : ‖u - v‖ = 0 := le_antisymm h (norm_nonneg (u - v))
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Section 3.1 (`eq:space_strain_corrector`) and Appendix A.3: the symmetric
gradient identifies the displacement and strain corrector spaces. The inverse
retains the full periodic H¹ bound from Korn's inequality. -/
theorem correctorGradient_equiv_exists (d : ℕ) :
    ∃ L : ZeroMeanPeriodicH1 d ≃L[ℝ] (correctorSubspace d).toSubmodule,
      (∀ u : ZeroMeanPeriodicH1 d, (L u : StrainField d) = correctorGradientL d u) ∧
      ∀ η : (correctorSubspace d).toSubmodule, ‖L.symm η‖ ≤ 2 * ‖η‖ := by
  let A : ZeroMeanPeriodicH1 d →L[ℝ] (correctorSubspace d).toSubmodule :=
    (correctorGradientL d).codRestrict (correctorSubspace d).toSubmodule (fun u => by
      rw [correctorSubspace_eq_range]
      exact ⟨u, rfl⟩)
  have hinj : Function.Injective A := by
    intro u v huv
    exact correctorGradient_injective d (congrArg Subtype.val huv)
  have hsurj : Function.Surjective A := by
    intro η
    have hη : (η : StrainField d) ∈ (correctorGradientL d).range := by
      simpa only [correctorSubspace_eq_range] using η.property
    obtain ⟨u, hu⟩ := hη
    exact ⟨u, Subtype.ext hu⟩
  let L := equivOfBijective (E := ZeroMeanPeriodicH1 d)
    (F := (correctorSubspace d).toSubmodule) A hinj hsurj
  have hL (u : ZeroMeanPeriodicH1 d) : (L u : StrainField d) = correctorGradientL d u := rfl
  refine ⟨L, hL, fun η => ?_⟩
  have hgrad : correctorGradientL d (L.symm η) = (η : StrainField d) :=
    (hL (L.symm η)).symm.trans (congrArg Subtype.val (L.apply_symm_apply η))
  calc
    ‖L.symm η‖ ≤ 2 * ‖correctorGradientL d (L.symm η)‖ := periodic_korn_two (L.symm η)
    _ = 2 * ‖η‖ := by rw [hgrad]; rfl

end KVApproximation.Homogenization
