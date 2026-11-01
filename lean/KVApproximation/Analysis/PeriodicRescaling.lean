module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Periodic rescaling of measurable fields

Projection preserves measure on each half-open unit cube. Countably many
integer translates cover physical space, so cell-null sets have null preimages.
The subsequent nonzero dilation preserves this property.
-/

public section

open MeasureTheory Set

namespace KVApproximation.Analysis

private theorem measurePreserving_coordinateCube {d : ℕ} (a : Fin d → ℝ) :
    MeasurePreserving (fun x : Fin d → ℝ => (fun i => (x i : UnitAddCircle)))
      (volume.restrict (Set.univ.pi fun i => Ioc (a i) (a i + 1))) (cellMeasure d) := by
  change MeasurePreserving _
    ((Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict _) _
  rw [Measure.restrict_pi_pi]
  apply measurePreserving_pi
  intro i
  simpa [volume, AddCircle.haarAddCircle] using AddCircle.measurePreserving_mk 1 (a i)

private theorem coordinateCubes_cover (d : ℕ) :
    (⋃ z : Fin d → ℤ, Set.univ.pi fun i => Ioc (z i : ℝ) ((z i : ℝ) + 1)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨fun i => Int.ceil (x i) - 1, ?_⟩
  intro i _
  simp only [Int.cast_sub, Int.cast_one, sub_add_cancel]
  exact ⟨by linarith [Int.ceil_lt_add_one (x i)], Int.le_ceil (x i)⟩

private theorem quasiMeasurePreserving_coordinates (d : ℕ) :
    QuasiMeasurePreserving
      (fun x : Fin d → ℝ => (fun i => (x i : UnitAddCircle)))
      volume (cellMeasure d) := by
  let q : (Fin d → ℝ) → PeriodicCell d := fun x i => (x i : UnitAddCircle)
  have hq : Measurable q :=
    Measurable.of_eval fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)
  refine ⟨hq, Measure.AbsolutelyContinuous.mk fun s hs hnull => ?_⟩
  rw [Measure.map_apply hq hs]
  have hcell : ∀ᵐ y ∂cellMeasure d, y ∉ s := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnull
  have hlocal (z : Fin d → ℤ) :
      ∀ᵐ x ∂volume.restrict (Set.univ.pi fun i => Ioc (z i : ℝ) ((z i : ℝ) + 1)),
        q x ∉ s := by
    exact (measurePreserving_coordinateCube (fun i => (z i : ℝ))).quasiMeasurePreserving.ae
      hcell
  have hall : ∀ᵐ x : Fin d → ℝ ∂volume.restrict
      (⋃ z : Fin d → ℤ, Set.univ.pi fun i => Ioc (z i : ℝ) ((z i : ℝ) + 1)),
      q x ∉ s := (ae_restrict_iUnion_iff
    (fun z : Fin d → ℤ => Set.univ.pi fun i => Ioc (z i : ℝ) ((z i : ℝ) + 1))
    (fun x => q x ∉ s)).mpr hlocal
  rw [coordinateCubes_cover, Measure.restrict_univ] at hall
  simpa only [ae_iff, not_not, Set.preimage] using hall

/-- Theorem 3.1, periodic coefficients: projection to the unit torus
pulls cell-null sets back to Lebesgue-null sets in physical space. -/
theorem quasiMeasurePreserving_toCell (d : ℕ) :
    QuasiMeasurePreserving (@toCell d) volume (cellMeasure d) := by
  exact (quasiMeasurePreserving_coordinates d).comp
    (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving

/-- Theorem 3.1, microscopic coefficients: every nonzero spatial scale
preserves null sets when followed by projection to the periodic cell. -/
theorem quasiMeasurePreserving_scaledToCell {d : ℕ} {ε : ℝ} (hε : ε ≠ 0) :
    QuasiMeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => toCell (ε⁻¹ • x))
      volume (cellMeasure d) := by
  exact (quasiMeasurePreserving_toCell d).comp
    (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hε))

/-- Theorem 3.1, coefficient hypotheses: every almost-everywhere cell
property remains valid for the periodically rescaled field. -/
theorem ae_rescalePeriodic {d : ℕ} {F : Type*} {A : PeriodicCell d → F}
    {P : F → Prop} {ε : ℝ} (hε : ε ≠ 0)
    (hA : ∀ᵐ y ∂cellMeasure d, P (A y)) :
    ∀ᵐ x ∂volume, P (rescalePeriodic A ε x) := by
  exact (quasiMeasurePreserving_scaledToCell hε).ae hA

/-- Theorem 3.1, microscopic coefficients: periodic rescaling preserves
almost-everywhere strong measurability at every nonzero scale. -/
theorem aestronglyMeasurable_rescalePeriodic {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {A : PeriodicCell d → F} {ε : ℝ} (hε : ε ≠ 0)
    (hA : AEStronglyMeasurable A (cellMeasure d)) :
    AEStronglyMeasurable (rescalePeriodic A ε) volume := by
  exact hA.comp_quasiMeasurePreserving (quasiMeasurePreserving_scaledToCell hε)

/-- Theorem 3.1, uniform coefficient bound: periodic rescaling does not
increase the essential supremum norm, independently of the scale. -/
theorem eLpNorm_top_rescalePeriodic_le {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {A : PeriodicCell d → F} {ε : ℝ} (hε : ε ≠ 0)
    (hA : AEStronglyMeasurable A (cellMeasure d)) :
    eLpNorm (rescalePeriodic A ε) ⊤ volume ≤ eLpNorm A ⊤ (cellMeasure d) := by
  rw [eLpNorm_exponent_top (aestronglyMeasurable_rescalePeriodic hε hA),
    eLpNorm_exponent_top hA]
  exact eLpNormEssSup_le_of_ae_enorm_bound
    (ae_rescalePeriodic (A := A) (P := fun z => ‖z‖ₑ ≤ eLpNormEssSup A (cellMeasure d))
      hε (ae_le_eLpNormEssSup (f := A)))

/-- Theorem 3.1, microscopic coefficients: every essentially bounded
periodic field defines an essentially bounded physical field. -/
theorem memLp_top_rescalePeriodic {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {A : PeriodicCell d → F} {ε : ℝ} (hε : ε ≠ 0)
    (hA : MemLp A ⊤ (cellMeasure d)) :
    MemLp (rescalePeriodic A ε) ⊤ volume := by
  exact (eLpNorm_top_rescalePeriodic_le hε hA.aestronglyMeasurable).trans_lt hA.eLpNorm_lt_top

end KVApproximation.Analysis
