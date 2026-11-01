module

public import KVApproximation.Homogenization.CellDisplacementEquivalence
public import KVApproximation.Homogenization.CellDisplacementStress
public import KVApproximation.Homogenization.CellConstitutive
public import KVApproximation.Dynamics.CellEvolutionConstitutive

/-!
# The constitutive law of the spatially averaged cell stress
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Dynamics

namespace KVApproximation.Homogenization

/-- Appendix A.3: the velocity of an H¹ trajectory is integrable on every
initial subinterval. -/
private theorem velocity_intervalIntegrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : ℝ} (e : TimeH1 H T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    IntervalIntegrable (TimeH1.velocity (H := H) (T := T) e) volume 0 t := by
  have hi : IntegrableOn (TimeH1.velocity (H := H) (T := T) e) (Ioo 0 T) :=
    (TimeH1.velocity_memLp (H := H) (T := T) e).integrable (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le).2
    (hi.mono_set (Ioo_subset_Ioo le_rfl ht.2.le))

/-- Appendix A.3: the tensor constitutive identity follows from all strain pairings. -/
private theorem constitutive_of_pairings {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) (t : ℝ) (u v w : Symmetric d)
    (f : ℝ → Symmetric d)
    (hf : IntervalIntegrable (fun s => action (C.kernel (t - s)) (f s)) volume 0 t)
    (h : ∀ a : Symmetric d, ⟪a, w⟫_ℝ = effectiveForm V a v + effectiveForm E a u +
      ∫ s in (0 : ℝ)..t, cellMemoryForm V E (t - s) a (f s)) :
    w = action C.viscosity v + action C.elasticity u +
      ∫ s in (0 : ℝ)..t, action (C.kernel (t - s)) (f s) := by
  apply ext_inner_left ℝ
  intro a
  rw [h a, inner_add_right (𝕜 := ℝ), inner_add_right (𝕜 := ℝ),
    C.viscosity_eq, C.elasticity_eq]
  congr 1
  calc
    _ = ∫ s in (0 : ℝ)..t, (innerSL ℝ a) (action (C.kernel (t - s)) (f s)) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact (C.kernel_eq (t - s) a (f s)).symm
    _ = _ := (innerSL ℝ a).intervalIntegral_comp_comm hf

/-- Appendix A.3 and Remark 3.2: eliminating the displacement cell solution
gives the exact positive-memory constitutive law for its actual spatially
averaged stress. -/
theorem periodicCellSolution_constitutive {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {T : ℝ} (hT : 0 < T)
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (hχ : IsPeriodicCellSolution (d := d) (T := T) V E hT e χ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      averagedCellStress (d := d) (T := T) V E e χ t =
        action C.viscosity (TimeH1.velocity (H := Symmetric d) (T := T) e t) +
          action C.elasticity (TimeH1.value (H := Symmetric d) (T := T) e t) +
            ∫ s in (0 : ℝ)..t,
              action (C.kernel (t - s)) (TimeH1.velocity (H := Symmetric d) (T := T) e s) := by
  obtain ⟨η, hη, _⟩ := displacement_strain_exists_unique (d := d) (T := T) χ
  have hiff := @periodicCellSolution_iff_evolution d V E T hT e χ η hη
  have he := hiff.mp hχ
  have hp := averagedCellStress_pairing V E (T := T) e χ η hη
  have hc := cell_evolution_constitutive_law (H := StrainField d) (F := Symmetric d)
    V.toForm E.toForm (correctorSubspace d) (constantStrainL d) (T := T) hT e η he
  refine ((hp.and hc).and (ae_restrict_mem measurableSet_Ioo)).mono ?_
  intro t ht
  have htime : t ∈ Ioo (0 : ℝ) T := ht.2
  have hv : IntervalIntegrable (TimeH1.velocity (H := Symmetric d) (T := T) e) volume 0 t :=
    velocity_intervalIntegrable (H := Symmetric d) (T := T) e htime
  have hk : Continuous (fun s : ℝ => actionL d (C.kernel (t - s))) :=
    (actionL d).continuous.comp ((cellKernel_continuous V E C).comp
      (continuous_const.sub continuous_id))
  have hki : IntervalIntegrable
      (fun s => action (C.kernel (t - s)) (TimeH1.velocity (H := Symmetric d) (T := T) e s))
      volume 0 t := intervalIntegrable_continuous_clm_apply hk.continuousOn hv
  exact constitutive_of_pairings V E C t
    (TimeH1.value (H := Symmetric d) (T := T) e t)
    (TimeH1.velocity (H := Symmetric d) (T := T) e t)
    (averagedCellStress (d := d) (T := T) V E e χ t)
    (TimeH1.velocity (H := Symmetric d) (T := T) e) hki
    (fun a => (ht.1.1 a).trans (ht.1.2 a))

end KVApproximation.Homogenization
