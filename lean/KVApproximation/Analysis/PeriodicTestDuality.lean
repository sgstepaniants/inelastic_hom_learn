module

public import KVApproximation.Analysis.PeriodicSmoothDensity
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Smooth periodic tests for the L¹ norm

Normalize a smooth approximation by `sqrt (‖g‖² + η²)`. The resulting smooth
test has norm at most one and loses at most `η` in its pairing with `g`.
-/

public section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The bounded tests used in the B.2 translation argument pair integrably
with every L¹ field. -/
private theorem integrable_inner_unit_test {f : PeriodicCell d → F}
    (hf : Integrable f (cellMeasure d)) (ψ : PeriodicC1 d F)
    (hψ : ∀ y, ‖ψ.value y‖ ≤ 1) :
    Integrable (fun y => ⟪f y, ψ.value y⟫_ℝ) (cellMeasure d) := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.inner ψ.continuous_value.aestronglyMeasurable)
  exact Eventually.of_forall fun y => (norm_inner_le_norm _ _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hψ y) (norm_nonneg (f y)))

omit [FiniteDimensional ℝ F] in
/-- Smooth normalization in the B.2 test-duality argument. The positive
regularization parameter keeps the denominator away from zero. -/
private theorem exists_normalized_periodic_test (g : PeriodicC1 d F)
    {η : ℝ} (hη : 0 < η) :
    ∃ ψ : PeriodicC1 d F, (∀ y, ‖ψ.value y‖ ≤ 1) ∧
      ∀ y, ‖g.value y‖ - η ≤ ⟪g.value y, ψ.value y⟫_ℝ := by
  have hpos (x : F) : 0 < ‖x‖ ^ 2 + η ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη)
  have hroot (x : F) : 0 < Real.sqrt (‖x‖ ^ 2 + η ^ 2) :=
    Real.sqrt_pos.mpr (hpos x)
  let ψ : PeriodicC1 d F :=
    ⟨fun y => (Real.sqrt (‖g.value y‖ ^ 2 + η ^ 2))⁻¹ • g.value y,
      (((g.contDiff_lift.norm_sq ℝ).add contDiff_const).sqrt
        (fun x => (hpos (g.value (toCell x))).ne')).inv
        (fun x => (hroot (g.value (toCell x))).ne') |>.smul g.contDiff_lift⟩
  have hle (x : F) : ‖x‖ ≤ Real.sqrt (‖x‖ ^ 2 + η ^ 2) := by
    calc
      ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖x‖ ^ 2 + η ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hηle (x : F) : η ≤ Real.sqrt (‖x‖ ^ 2 + η ^ 2) := by
    calc
      η = Real.sqrt (η ^ 2) := (Real.sqrt_sq hη.le).symm
      _ ≤ Real.sqrt (‖x‖ ^ 2 + η ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  refine ⟨ψ, fun y => ?_, fun y => ?_⟩
  · change ‖(Real.sqrt (‖g.value y‖ ^ 2 + η ^ 2))⁻¹ • g.value y‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hroot _), ← div_eq_inv_mul]
    exact (div_le_one (hroot _)).2 (hle _)
  · change ‖g.value y‖ - η ≤
      ⟪g.value y, (Real.sqrt (‖g.value y‖ ^ 2 + η ^ 2))⁻¹ • g.value y⟫_ℝ
    rw [inner_smul_right, real_inner_self_eq_norm_sq, ← div_eq_inv_mul]
    apply (le_div_iff₀ (hroot _)).2
    have hsquare := Real.sq_sqrt (hpos (g.value y)).le
    have hr := mul_le_mul_of_nonneg_right (hle (g.value y)) (hroot (g.value y)).le
    have hηr := mul_le_mul_of_nonneg_left (hηle (g.value y)) hη.le
    nlinarith

/-- Lemma B.2, periodic BV embedding: the L¹ norm is determined by smooth
periodic tests bounded pointwise by one, in the original target norm. -/
theorem eLpNorm_one_eq_iSup_periodicTestPairing (A : Lp F 1 (cellMeasure d)) :
    eLpNorm A 1 (cellMeasure d) =
      ⨆ (φ : PeriodicC1 d F) (_hφ : ∀ y, ‖φ.value y‖ ≤ 1),
        ENNReal.ofReal (∫ y, ⟪A y, φ.value y⟫_ℝ ∂cellMeasure d) := by
  let R : ENNReal := ⨆ (φ : PeriodicC1 d F) (_hφ : ∀ y, ‖φ.value y‖ ≤ 1),
    ENNReal.ofReal (∫ y, ⟪A y, φ.value y⟫_ℝ ∂cellMeasure d)
  have hA : Integrable A (cellMeasure d) := (Lp.memLp A).integrable (by simp)
  have hupper : R ≤ eLpNorm A 1 (cellMeasure d) := by
    apply iSup₂_le
    intro φ hφ
    have hp (y : PeriodicCell d) : ⟪A y, φ.value y⟫_ℝ ≤ ‖A y‖ := by
      apply (real_inner_le_norm _ _).trans
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hφ y) (norm_nonneg (A y))
    have hi := integral_mono_ae (integrable_inner_unit_test hA φ hφ) hA.norm
      (Eventually.of_forall hp)
    calc
      ENNReal.ofReal (∫ y, ⟪A y, φ.value y⟫_ℝ ∂cellMeasure d) ≤
          ENNReal.ofReal (∫ y, ‖A y‖ ∂cellMeasure d) := ENNReal.ofReal_le_ofReal hi
      _ = eLpNorm A 1 (cellMeasure d) := by
        rw [ofReal_integral_norm_eq_lintegral_enorm hA,
          eLpNorm_one_eq_lintegral_enorm hA.aestronglyMeasurable]
  apply le_antisymm ?_ hupper
  have hR : R ≠ ⊤ := (hupper.trans_lt (Lp.memLp A)).ne
  apply (ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top A) hR).1
  apply le_of_forall_pos_le_add
  intro ε hε
  have hη : 0 < ε / 3 := by linarith
  obtain ⟨g, hg⟩ := exists_periodicC1_eLpNorm_sub_lt A hη
  obtain ⟨ψ, hψ, hpair⟩ := exists_normalized_periodic_test g hη
  have hgint : Integrable g.value (cellMeasure d) :=
    g.continuous_value.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdiff : Integrable (fun y => A y - g.value y) (cellMeasure d) := hA.sub hgint
  have herror : (∫ y, ‖A y - g.value y‖ ∂cellMeasure d) ≤ ε / 3 := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
    rw [ENNReal.toReal_ofReal hη.le,
      eLpNorm_one_eq_lintegral_enorm hdiff.aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm hdiff.aestronglyMeasurable] at ht
    exact ht
  have hψR : (∫ y, ⟪A y, ψ.value y⟫_ℝ ∂cellMeasure d) ≤ R.toReal := by
    have ht := ENNReal.toReal_mono hR
      (le_iSup_of_le ψ (le_iSup_of_le hψ le_rfl))
    exact (le_max_left _ 0).trans ht
  have hpoint (y : PeriodicCell d) : ‖A y‖ ≤
      ⟪A y, ψ.value y⟫_ℝ + (2 * ‖A y - g.value y‖ + ε / 3) := by
    have htri : ‖A y‖ ≤ ‖A y - g.value y‖ + ‖g.value y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (A y - g.value y) (g.value y)
    have hi : ⟪g.value y - A y, ψ.value y⟫_ℝ ≤ ‖A y - g.value y‖ := by
      calc
        _ ≤ ‖g.value y - A y‖ * ‖ψ.value y‖ := real_inner_le_norm _ _
        _ ≤ ‖g.value y - A y‖ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hψ y) (norm_nonneg (g.value y - A y))
        _ = ‖A y - g.value y‖ := norm_sub_rev _ _
    rw [inner_sub_left] at hi
    linarith [hpair y]
  have hi := integrable_inner_unit_test hA ψ hψ
  have hm := integral_mono_ae hA.norm
    (hi.add ((hdiff.norm.const_mul 2).add (integrable_const (ε / 3))))
    (Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at hm
  rw [integral_add (g := fun y => 2 * ‖A y - g.value y‖ + ε / 3)
      hi ((hdiff.norm.const_mul 2).add (integrable_const (ε / 3))),
    integral_add (hdiff.norm.const_mul 2) (integrable_const (ε / 3)), integral_const_mul] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  rw [eLpNorm_one_eq_lintegral_enorm hA.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hA.aestronglyMeasurable]
  linarith

end KVApproximation.Analysis
