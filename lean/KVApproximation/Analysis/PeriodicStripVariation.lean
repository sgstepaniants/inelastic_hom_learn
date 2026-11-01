module

public import KVApproximation.Analysis.PeriodicSlicing
public import KVApproximation.Analysis.PeriodicIntegration
public import KVApproximation.Analysis.PeriodicVariationStability

/-!
# Variation bounds for periodic strip fields
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Proposition 4.7, distributional tests: integrable coordinate
derivatives may be integrated before taking the finite divergence sum. -/
private theorem integral_divergence_eq_sum
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F)))
    {μ : Measure (PeriodicCell d)} (hφ : ∀ j, Integrable (φ.partial j) μ) :
    (∫ y, φ.divergence y ∂μ) = ∑ j : Fin d, (∫ y, φ.partial j y ∂μ) j := by
  unfold PeriodicC1.divergence
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => F) j).integral_comp_comm (hφ j)
  · intro j _
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => F) j).integrable_comp (hφ j)

/-- Proposition 4.7, periodic cancellation: a divergence has zero mean. -/
private theorem integral_divergence_eq_zero
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F))) :
    (∫ y, φ.divergence y ∂cellMeasure d) = 0 := by
  rw [integral_divergence_eq_sum φ (fun j =>
    (φ.continuous_partial j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [φ.integral_partial_eq_zero, PiLp.zero_apply, Finset.sum_const_zero]

/-- Proposition 4.7, constant coefficients: a constant pairing with a
periodic divergence integrates to zero. -/
private theorem integral_const_inner_divergence_eq_zero
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F))) (c : F) :
    (∫ y, ⟪c, φ.divergence y⟫_ℝ ∂cellMeasure d) = 0 := by
  have hint : Integrable φ.divergence (cellMeasure d) :=
    φ.continuous_divergence.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simpa only [innerSL_apply_apply, integral_divergence_eq_zero, inner_zero_right] using
    (innerSL ℝ c).integral_comp_comm hint

/-- Proposition 4.7, strip cancellation: only the normal derivative
contributes to the integral of a divergence over a coordinate strip. -/
private theorem norm_integral_coordinate_strip_divergence_le
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F))) (i : Fin d)
    {a : ℝ} (ha : 0 ≤ a) (ha_one : a ≤ 1) (hφ : ∀ y, ‖φ.value y‖ ≤ 1) :
    ‖∫ y in {y : PeriodicCell d | 0 < cellRepresentative y i ∧ cellRepresentative y i < a},
      φ.divergence y ∂cellMeasure d‖ ≤ 2 := by
  classical
  let s : Set (PeriodicCell d) :=
    {y | 0 < cellRepresentative y i ∧ cellRepresentative y i < a}
  have hint (j : Fin d) : Integrable (φ.partial j) ((cellMeasure d).restrict s) :=
    ((φ.continuous_partial j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).restrict
  have hnormal : (∫ y in s, φ.divergence y ∂cellMeasure d) =
      (∫ y in s, φ.partial i y ∂cellMeasure d) i := by
    rw [integral_divergence_eq_sum φ hint]
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hz : (∫ y in s, φ.partial j y ∂cellMeasure d) = 0 := by
        simpa only [ite_eq_right hji] using φ.integral_coordinate_strip_partial i j ha ha_one
      rw [hz]
      rfl
    · simp
  change ‖∫ y in s, φ.divergence y ∂cellMeasure d‖ ≤ 2
  rw [hnormal]
  exact (PiLp.norm_apply_le _ i).trans (by
    simpa only [mul_one] using φ.norm_integral_coordinate_strip_partial_le i i ha ha_one hφ)

/-- Proposition 4.7 (`prop:no_spectral_stability`), constant coefficients:
a constant periodic field has zero distributional variation. -/
theorem periodicVariation_const {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] (c : F) :
    periodicVariation (fun _ : PeriodicCell d => c) = 0 := by
  apply le_antisymm ?_ bot_le
  unfold periodicVariation
  apply iSup₂_le
  intro φ _
  rw [integral_const_inner_divergence_eq_zero φ c, ENNReal.ofReal_zero]
  exact le_rfl

/-- Proposition 4.7 (`prop:no_spectral_stability`), uniform strip bound:
adding a constant jump on an open coordinate strip contributes at most
twice its norm to variation, independently of the width and dimension. -/
theorem periodicVariation_const_add_coordinate_strip_le {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (i : Fin d) (c₀ c₁ : F) {a : ℝ} (ha : 0 ≤ a) (ha_one : a ≤ 1) :
    periodicVariation (fun y : PeriodicCell d => c₀ +
      {z : PeriodicCell d | 0 < cellRepresentative z i ∧ cellRepresentative z i < a}.indicator
        (fun _ => c₁) y) ≤ ENNReal.ofReal (2 * ‖c₁‖) := by
  classical
  let s : Set (PeriodicCell d) :=
    {y | 0 < cellRepresentative y i ∧ cellRepresentative y i < a}
  have hs : MeasurableSet s :=
    (measurePreserving_cellRepresentative_coordinate i).measurable measurableSet_Ioo
  unfold periodicVariation
  apply iSup₂_le
  intro φ hφ
  have hint : Integrable φ.divergence (cellMeasure d) :=
    φ.continuous_divergence.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconst : Integrable (fun y => ⟪c₀, φ.divergence y⟫_ℝ) (cellMeasure d) :=
    (innerSL ℝ c₀).integrable_comp hint
  have hjump : Integrable (s.indicator (fun y => ⟪c₁, φ.divergence y⟫_ℝ))
      (cellMeasure d) := ((innerSL ℝ c₁).integrable_comp hint).indicator hs
  have heq (y : PeriodicCell d) :
      ⟪c₀ + s.indicator (fun _ => c₁) y, φ.divergence y⟫_ℝ =
        ⟪c₀, φ.divergence y⟫_ℝ + s.indicator (fun y => ⟪c₁, φ.divergence y⟫_ℝ) y := by
    by_cases hy : y ∈ s <;> simp [Set.indicator, hy, inner_add_left]
  have hpair : (∫ y, ⟪c₀ + s.indicator (fun _ => c₁) y, φ.divergence y⟫_ℝ
      ∂cellMeasure d) = ⟪c₁, ∫ y in s, φ.divergence y ∂cellMeasure d⟫_ℝ := by
    simp_rw [heq]
    rw [integral_add hconst hjump, integral_const_inner_divergence_eq_zero φ c₀,
      zero_add, integral_indicator hs]
    simpa only [innerSL_apply_apply] using (innerSL ℝ c₁).integral_comp_comm hint.restrict
  change ENNReal.ofReal (∫ y, ⟪c₀ + s.indicator (fun _ => c₁) y, φ.divergence y⟫_ℝ
    ∂cellMeasure d) ≤ _
  rw [hpair]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ‖c₁‖ * ‖∫ y in s, φ.divergence y ∂cellMeasure d‖ := real_inner_le_norm _ _
    _ ≤ ‖c₁‖ * 2 := mul_le_mul_of_nonneg_left
      (norm_integral_coordinate_strip_divergence_le φ i ha ha_one hφ) (norm_nonneg _)
    _ = 2 * ‖c₁‖ := mul_comm _ _

end KVApproximation.Analysis
