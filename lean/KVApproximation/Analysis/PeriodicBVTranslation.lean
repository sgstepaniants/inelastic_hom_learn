module

public import KVApproximation.Analysis.PeriodicTranslationTests
public import KVApproximation.Analysis.PeriodicTestDuality
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation estimate for periodic bounded variation

Smooth test duality and Haar translation turn the divergence construction into
the exact L¹ translation estimate. The variation may be infinite.
-/

public section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Lemma B.2, integration of the unit-bounded tests in the translation argument. -/
private theorem integrable_pairing_of_unit_bound {B g : PeriodicCell d → F}
    (hB : Integrable B (cellMeasure d)) (hg : Continuous g) (hb : ∀ y, ‖g y‖ ≤ 1) :
    Integrable (fun y => ⟪B y, g y⟫_ℝ) (cellMeasure d) := by
  apply hB.norm.mono' (hB.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact Eventually.of_forall fun y => (norm_inner_le_norm _ _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb y) (norm_nonneg (B y)))

/-- Lemma B.2 (`lem:bv_compact`), translation criterion for the cited BV
embedding: translation by a Euclidean vector is controlled by its length and
the original isotropic periodic variation. -/
theorem periodicVariation_translation_bound (A : Lp F 1 (cellMeasure d))
    (v : EuclideanSpace ℝ (Fin d)) :
    eLpNorm (fun y => A (y + toCell v) - A y) 1 (cellMeasure d) ≤
      ENNReal.ofReal ‖v‖ * periodicVariation A := by
  let : (cellMeasure d).IsAddHaarMeasure := by unfold cellMeasure; infer_instance
  by_cases hv : v = 0
  · subst v
    have hzero : toCell (0 : EuclideanSpace ℝ (Fin d)) = 0 := by ext i; rfl
    simp [hzero]
  have hr : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hA := (Lp.memLp A).integrable (by simp)
  have htrans := (Lp.memLp A).comp_measurePreserving
    (measurePreserving_add_right (cellMeasure d) (toCell v))
  have hmem : MemLp (fun y => A (y + toCell v) - A y) 1 (cellMeasure d) :=
    htrans.sub (Lp.memLp A)
  let B : Lp F 1 (cellMeasure d) := hmem.toLp _
  have hB : (B : PeriodicCell d → F) =ᵐ[cellMeasure d]
      fun y => A (y + toCell v) - A y := hmem.coeFn_toLp
  rw [← eLpNorm_congr_ae hB, eLpNorm_one_eq_iSup_periodicTestPairing]
  apply iSup₂_le
  intro g hg
  obtain ⟨ψ, hψ, hdivψ⟩ := exists_periodic_divergence_eq_translate_sub g hg v
  let χ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F)) :=
    ⟨fun y => ‖v‖⁻¹ • ψ.value y, ψ.contDiff_lift.const_smul _⟩
  have hχ : ∀ y, ‖χ.value y‖ ≤ 1 := by
    intro y
    change ‖‖v‖⁻¹ • ψ.value y‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    calc
      ‖v‖⁻¹ * ‖ψ.value y‖ ≤ ‖v‖⁻¹ * ‖v‖ :=
        mul_le_mul_of_nonneg_left (hψ y) (inv_nonneg.2 hr.le)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  have hdivχ (y : PeriodicCell d) : χ.divergence y = ‖v‖⁻¹ • ψ.divergence y := by
    have hderiv := ((ψ.contDiff_lift.differentiable_one (cellRepresentative y)).hasFDerivAt.const_smul
      (‖v‖⁻¹)).fderiv
    change fderiv ℝ (fun x => ‖v‖⁻¹ • ψ.value (toCell x)) (cellRepresentative y) =
      ‖v‖⁻¹ • fderiv ℝ (fun x => ψ.value (toCell x)) (cellRepresentative y) at hderiv
    change (∑ i : Fin d,
      (fderiv ℝ (fun x => ‖v‖⁻¹ • ψ.value (toCell x)) (cellRepresentative y)
        (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) i) = _
    rw [hderiv]
    simp only [smul_apply, PiLp.smul_apply, ← Finset.smul_sum]
    rfl
  have hpair : (∫ y, ⟪B y, g.value y⟫_ℝ ∂cellMeasure d) =
      ∫ y, ⟪A y, ψ.divergence y⟫_ℝ ∂cellMeasure d := by
    have hshift := integral_add_right_eq_self (μ := cellMeasure d)
      (fun y => ⟪A y, g.value (y - toCell v)⟫_ℝ) (toCell v)
    simp only [add_sub_cancel_right] at hshift
    have hi := integrable_pairing_of_unit_bound hA g.continuous_value hg
    have ht := integrable_pairing_of_unit_bound
      (htrans.integrable (by simp)) g.continuous_value hg
    have hs := integrable_pairing_of_unit_bound (g := fun y => g.value (y - toCell v)) hA
      (g.continuous_value.comp (continuous_id.sub continuous_const)) (fun y => hg _)
    calc
      (∫ y, ⟪B y, g.value y⟫_ℝ ∂cellMeasure d) =
          ∫ y, ⟪A (y + toCell v) - A y, g.value y⟫_ℝ ∂cellMeasure d := by
        apply integral_congr_ae
        filter_upwards [hB] with y hy
        rw [hy]
      _ = (∫ y, ⟪A (y + toCell v), g.value y⟫_ℝ ∂cellMeasure d) -
          ∫ y, ⟪A y, g.value y⟫_ℝ ∂cellMeasure d := by
        simp_rw [inner_sub_left]
        exact integral_sub ht hi
      _ = ∫ y, ⟪A y, g.value (y - toCell v) - g.value y⟫_ℝ ∂cellMeasure d := by
        rw [hshift, ← integral_sub hs hi]
        congr 1
        funext y
        exact (inner_sub_right _ _ _).symm
      _ = ∫ y, ⟪A y, ψ.divergence y⟫_ℝ ∂cellMeasure d := by
        simp only [hdivψ]
  have hscale : (∫ y, ⟪A y, ψ.divergence y⟫_ℝ ∂cellMeasure d) =
      ‖v‖ * ∫ y, ⟪A y, χ.divergence y⟫_ℝ ∂cellMeasure d := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change ⟪A y, ψ.divergence y⟫_ℝ = ‖v‖ * ⟪A y, χ.divergence y⟫_ℝ
      rw [hdivχ, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hpair, hscale, ENNReal.ofReal_mul hr.le]
  apply mul_le_mul_right
  exact le_iSup_of_le χ (le_iSup_of_le hχ le_rfl)

end KVApproximation.Analysis
