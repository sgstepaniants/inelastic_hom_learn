module

public import KVApproximation.Analysis.PeriodicDistributionalGradient
public import KVApproximation.Analysis.PeriodicVariationStability

/-!
# Periodic Sobolev bounds imply bounded variation

Integration by parts transfers each unit variation test to the gradient.
Cauchy–Schwarz and the normalized cell measure give the bound for every p ≥ 1.
-/

public section

open MeasureTheory Filter
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Remark 4.1 (Bounded Variation): the dual variation is bounded by the
Lp norm of the actual distributional gradient for every 1 ≤ p ≤ ∞. -/
theorem periodicVariation_le_eLpNorm_gradient {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : PeriodicCell d → F} {G : PeriodicCell d → PiLp 2 (fun _ : Fin d => F)}
    {p : ENNReal} (hp : 1 ≤ p) (hG : MemLp G p (cellMeasure d))
    (hgrad : HasPeriodicDistributionalGradient A G) :
    periodicVariation A ≤ eLpNorm G p (cellMeasure d) := by
  have hG1 : Integrable G (cellMeasure d) := hG.integrable hp
  unfold periodicVariation
  apply iSup₂_le
  intro φ hφ
  have hpoint (y : PeriodicCell d) : ‖⟪G y, φ.value y⟫_ℝ‖ ≤ ‖G y‖ :=
    (norm_inner_le_norm _ _).trans (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hφ y) (norm_nonneg (G y)))
  have hi : Integrable (fun y => ⟪G y, φ.value y⟫_ℝ) (cellMeasure d) :=
    hG1.norm.mono'
      (hG1.aestronglyMeasurable.inner φ.continuous_value.aestronglyMeasurable)
      (Eventually.of_forall hpoint)
  rw [hgrad φ]
  calc
    ENNReal.ofReal (-(∫ y, ⟪G y, φ.value y⟫_ℝ ∂cellMeasure d)) ≤
        ENNReal.ofReal (∫ y, ‖G y‖ ∂cellMeasure d) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        -(∫ y, ⟪G y, φ.value y⟫_ℝ ∂cellMeasure d) ≤
            ‖∫ y, ⟪G y, φ.value y⟫_ℝ ∂cellMeasure d‖ := by
          simpa only [Real.norm_eq_abs] using
            neg_le_abs (∫ y, ⟪G y, φ.value y⟫_ℝ ∂cellMeasure d)
        _ ≤ ∫ y, ‖⟪G y, φ.value y⟫_ℝ‖ ∂cellMeasure d :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ y, ‖G y‖ ∂cellMeasure d :=
          integral_mono_ae hi.norm hG1.norm (Eventually.of_forall hpoint)
    _ = eLpNorm G 1 (cellMeasure d) := by
      rw [ofReal_integral_norm_eq_lintegral_enorm hG1,
        eLpNorm_one_eq_lintegral_enorm hG1.aestronglyMeasurable]
    _ ≤ eLpNorm G p (cellMeasure d) := eLpNorm_le_eLpNorm_of_exponent_le hp

/-- Remark 4.1 (Bounded Variation): the additive value/gradient Sobolev
bound controls the paper's L¹-plus-variation norm with constant one. -/
theorem periodicBVNorm_le_sobolevBound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A : PeriodicCell d → F} {G : PeriodicCell d → PiLp 2 (fun _ : Fin d => F)}
    {p : ENNReal} (hp : 1 ≤ p) (_hA : MemLp A p (cellMeasure d))
    (hG : MemLp G p (cellMeasure d)) (hgrad : HasPeriodicDistributionalGradient A G) :
    periodicBVNorm A ≤ eLpNorm A p (cellMeasure d) + eLpNorm G p (cellMeasure d) := by
  exact add_le_add (eLpNorm_le_eLpNorm_of_exponent_le hp)
    (periodicVariation_le_eLpNorm_gradient hp hG hgrad)

end KVApproximation.Analysis
