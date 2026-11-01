module

public import KVApproximation.Homogenization.CorrectorTrajectory
public import KVApproximation.Homogenization.CorrectorDisplacement
public import KVApproximation.Analysis.TimeSobolevMaps

/-!
# Recovery of periodic displacement trajectories
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

section Transport

variable {U X Z : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Appendix A.3: spatial maps identify both components of a time-Sobolev jet. -/
private def MapsTrajectory (G : U →L[ℝ] Z) (J : X →L[ℝ] Z) {T : ℝ}
    (u : TimeH1 U T) (x : TimeH1 X T) : Prop :=
  ((fun t => J (TimeH1.value (H := X) (T := T) x t)) =ᵐ[volume.restrict (Set.Ioo 0 T)]
    fun t => G (TimeH1.value (H := U) (T := T) u t)) ∧
  ((fun t => J (TimeH1.velocity (H := X) (T := T) x t)) =ᵐ[volume.restrict (Set.Ioo 0 T)]
    fun t => G (TimeH1.velocity (H := U) (T := T) u t))

/-- Appendix A.3: forward transport through the spatial equivalence. -/
private theorem forward_trajectory (L : U ≃L[ℝ] X) (G : U →L[ℝ] Z)
    (J : X →L[ℝ] Z) (hL : ∀ u, J (L u) = G u) (hJ : Function.Injective J)
    {T : ℝ} (u : TimeH1 U T) :
    ∃! x : TimeH1 X T, MapsTrajectory (T := T) G J u x := by
  have hmap := @TimeH1.exists_map U X inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance L.toContinuousLinearMap T u
  obtain ⟨x, hv, hd⟩ := hmap
  have hx : MapsTrajectory (T := T) G J u x := by
    constructor
    · filter_upwards [hv] with t ht
      exact (congrArg J ht).trans (hL _)
    · filter_upwards [hd] with t ht
      exact (congrArg J ht).trans (hL _)
  refine ⟨x, hx, fun y hy => ?_⟩
  apply TimeH1.eq_of_value_ae (H := X) (T := T)
  filter_upwards [hy.1, hx.1] with t hyt hxt
  exact hJ (hyt.trans hxt.symm)

/-- Appendix A.3: inverse transport through the spatial equivalence. -/
private theorem inverse_trajectory (L : U ≃L[ℝ] X) (G : U →L[ℝ] Z)
    (J : X →L[ℝ] Z) (hL : ∀ u, J (L u) = G u) (hG : Function.Injective G)
    {T : ℝ} (x : TimeH1 X T) :
    ∃! u : TimeH1 U T, MapsTrajectory (T := T) G J u x := by
  have hgrad (a : X) : G (L.symm a) = J a :=
    (hL (L.symm a)).symm.trans (congrArg J (L.apply_symm_apply a))
  have hmap := @TimeH1.exists_map X U inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance L.symm.toContinuousLinearMap T x
  obtain ⟨u, hv, hd⟩ := hmap
  have hu : MapsTrajectory (T := T) G J u x := by
    constructor
    · filter_upwards [hv] with t ht
      exact ((congrArg G ht).trans (hgrad _)).symm
    · filter_upwards [hd] with t ht
      exact ((congrArg G ht).trans (hgrad _)).symm
  refine ⟨u, hu, fun v hv => ?_⟩
  apply TimeH1.eq_of_value_ae (H := U) (T := T)
  filter_upwards [hv.1, hu.1] with t hvt hut
  exact hG (hvt.symm.trans hut)

/-- Appendix A.3: the same spatial identification holds on continuous traces. -/
private theorem trajectory_trace (L : U ≃L[ℝ] X) (G : U →L[ℝ] Z)
    (J : X →L[ℝ] Z) (hL : ∀ u, J (L u) = G u) (hJ : Function.Injective J)
    {T : ℝ} (hT : 0 < T) (u : TimeH1 U T) (x : TimeH1 X T)
    (h : MapsTrajectory (T := T) G J u x) (t : Set.Icc (0 : ℝ) T) :
    J (TimeH1.trace (H := X) (T := T) hT x t) = G (TimeH1.trace (H := U) (T := T) hT u t) := by
  have hv : TimeH1.value (H := X) (T := T) x =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fun s => L (TimeH1.value (H := U) (T := T) u s) := by
    filter_upwards [h.1] with s hs
    exact hJ (hs.trans (hL _).symm)
  have ht := @TimeH1.trace_map_of_value_ae U X inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance L.toContinuousLinearMap T hT u x hv t
  exact (congrArg J ht).trans (hL _)

end Transport

/-- Section 3.1 (`eq:strain_corrector`) and Appendix A.3: a periodic
H¹ displacement trajectory has a unique strain-corrector trajectory. -/
theorem displacement_strain_exists_unique {d : ℕ} {T : ℝ}
    (χ : TimeH1 (ZeroMeanPeriodicH1 d) T) :
    ∃! η : TimeH1 (correctorSubspace d) T, IsDisplacementStrain (d := d) (T := T) χ η := by
  let L := (correctorGradient_equiv_exists d).choose
  have hL := (correctorGradient_equiv_exists d).choose_spec.1
  have h := @forward_trajectory (ZeroMeanPeriodicH1 d)
    (correctorSubspace d) (StrainField d)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance L (correctorGradientL d)
    (correctorSubspace d).toSubmodule.subtypeL hL
    (fun _ _ h => Subtype.ext h) T χ
  exact h

/-- Section 3.1 (`eq:strain_corrector`) and Appendix A.3: every finite-time
H¹ strain-corrector trajectory comes from a unique zero-mean periodic
displacement trajectory, with the corresponding weak time derivative. -/
theorem strain_displacement_exists_unique {d : ℕ} {T : ℝ}
    (η : TimeH1 (correctorSubspace d) T) :
    ∃! χ : TimeH1 (ZeroMeanPeriodicH1 d) T, IsDisplacementStrain (d := d) (T := T) χ η := by
  let L := (correctorGradient_equiv_exists d).choose
  have hL := (correctorGradient_equiv_exists d).choose_spec.1
  have h := @inverse_trajectory (ZeroMeanPeriodicH1 d)
    (correctorSubspace d) (StrainField d)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance L (correctorGradientL d)
    (correctorSubspace d).toSubmodule.subtypeL hL (correctorGradient_injective d) T η
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Appendix A.3, initial preparation in `eq:cell_weak`: the symmetric-gradient
identification holds at every closed-interval time, including time zero. -/
theorem displacement_strain_trace {d : ℕ} {T : ℝ} (hT : 0 < T)
    (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (η : TimeH1 (correctorSubspace d) T)
    (h : IsDisplacementStrain (d := d) (T := T) χ η) (t : Set.Icc (0 : ℝ) T) :
    (@TimeH1.trace (correctorSubspace d) inferInstance inferInstance
      inferInstance T hT η t).val =
      correctorGradientL d (@TimeH1.trace (ZeroMeanPeriodicH1 d) inferInstance inferInstance
        inferInstance T hT χ t) := by
  let L := (correctorGradient_equiv_exists d).choose
  have hL := (correctorGradient_equiv_exists d).choose_spec.1
  have ht := @trajectory_trace (ZeroMeanPeriodicH1 d)
    (correctorSubspace d) (StrainField d)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance L (correctorGradientL d)
    (correctorSubspace d).toSubmodule.subtypeL hL
    (fun _ _ h => Subtype.ext h) T hT χ η h t
  exact ht

end KVApproximation.Homogenization
