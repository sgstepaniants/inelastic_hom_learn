module

public import KVApproximation.KelvinVoigt.StripFields
public import KVApproximation.Analysis.PeriodicCoordinates
public import KVApproximation.Tensor.FieldBounds
public import KVApproximation.Tensor.IsotropicIdentities
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Measures and measurability of thin-strip fields
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip construction:
the open strip is measurable for every positive shifted index. -/
theorem measurableSet_thinStrip {d : ℕ} (i : Fin d) (m : ℕ) :
    MeasurableSet (thinStrip i m) := by
  change MeasurableSet ((fun y : PeriodicCell d => cellRepresentative y i) ⁻¹'
    Set.Ioo (0 : ℝ) (1 / ((m : ℝ) + 1)))
  exact (measurePreserving_cellRepresentative_coordinate i).measurable measurableSet_Ioo

/-- Proposition 4.7 (`prop:no_spectral_stability`), coefficient convergence:
the strip has exactly its prescribed width in normalized cell measure,
including full measure when `m = 0`. -/
theorem cellMeasure_thinStrip {d : ℕ} (i : Fin d) (m : ℕ) :
    cellMeasure d (thinStrip i m) = ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
  have hpos : 0 < (m : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
  have hwidth : 1 / ((m : ℝ) + 1) ≤ 1 :=
    (div_le_one hpos).2 (le_add_of_nonneg_left (Nat.cast_nonneg m))
  simpa only [thinStrip, sub_zero] using
    cellMeasure_coordinate_interval i 0 (1 / ((m : ℝ) + 1)) le_rfl hwidth

/-- Proposition 4.7 (`prop:no_spectral_stability`), admissible coefficients:
the piecewise constant elasticity field is measurable. -/
theorem measurable_stripElasticity {d : ℕ} (i : Fin d) (m : ℕ) :
    Measurable (stripElasticity i m) := by
  classical
  change Measurable (fun y : PeriodicCell d =>
    ((1 : ℝ) + if y ∈ thinStrip i m then (1 : ℝ) else 0) • identityElasticity d)
  have hscalar : Measurable (fun y : PeriodicCell d =>
      (1 : ℝ) + (thinStrip i m).indicator (fun _ => (1 : ℝ)) y) :=
    measurable_const.add (measurable_const.indicator (measurableSet_thinStrip i m))
  simpa only [Set.indicator] using
    hscalar.smul_const (identityElasticity d)

/-- Proposition 4.7 (`prop:no_spectral_stability`), coefficient bounds:
the strip elasticity is essentially bounded in the actual Frobenius norm. -/
theorem memLp_stripElasticity {d : ℕ} (i : Fin d) (m : ℕ) :
    MemLp (stripElasticity i m) ⊤ (cellMeasure d) := by
  classical
  apply memLp_top_of_bound (measurable_stripElasticity i m).aestronglyMeasurable
    (2 * ‖identityElasticity d‖)
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : y ∈ thinStrip i m
  · simp only [stripElasticity, ite_eq_left hy, norm_smul, Real.norm_eq_abs]
    norm_num
  · simp only [stripElasticity, ite_eq_right hy, add_zero, one_smul]
    linarith [norm_nonneg (identityElasticity d)]

/-- Proposition 4.7 (`prop:no_spectral_stability`), ellipticity:
the strip elasticity has the exact common quadratic-form bounds one and two. -/
theorem hasFieldBounds_stripElasticity {d : ℕ} (i : Fin d) (m : ℕ) :
    HasFieldBounds 1 2 (stripElasticity i m) := by
  classical
  have hpoint (y : PeriodicCell d) : HasBounds 1 2 (stripElasticity i m y) := by
    intro e
    rw [← actionL_apply, stripElasticity, map_smul, smul_apply,
      actionL_apply, action_identityElasticity, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    split_ifs <;> constructor <;> nlinarith [sq_nonneg ‖e‖]
  let hA := memLp_stripElasticity i m
  have hb : HasFieldBounds 1 2 (hA.toLp (stripElasticity i m)) := by
    apply (hasFieldBounds_iff_ae _).2
    filter_upwards [hA.coeFn_toLp] with y hy
    rw [hy]
    exact hpoint y
  exact hb.congr hA.coeFn_toLp

end KVApproximation.KelvinVoigt
