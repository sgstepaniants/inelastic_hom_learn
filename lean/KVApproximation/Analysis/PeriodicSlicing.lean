module

public import KVApproximation.Analysis.PeriodicCoordinateUpdate
public import KVApproximation.Analysis.PeriodicCoordinates
public import KVApproximation.Analysis.PeriodicSmoothIdentities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Coordinate slices of periodic derivatives
-/

public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Proposition 4.7, slicing: joint coordinate replacement and Bochner
Fubini express an integrable cell field as the average of its fibres. -/
private theorem integral_coordinate_update
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : PeriodicCell d → F) (hf : Integrable f (cellMeasure d)) (i : Fin d) :
    (∫ y, f y ∂cellMeasure d) =
      ∫ y : PeriodicCell d, ∫ r : UnitAddCircle, f (Function.update y i r)
        ∂AddCircle.haarAddCircle ∂cellMeasure d := by
  have hU := measurePreserving_coordinate_update i
  have hprod : Integrable
      (fun z : PeriodicCell d × UnitAddCircle => f (Function.update z.1 i z.2))
      ((cellMeasure d).prod (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    simpa only [Function.comp_def] using hU.integrable_comp_of_integrable hf
  have hmeas : AEStronglyMeasurable f
      (Measure.map (fun z : PeriodicCell d × UnitAddCircle => Function.update z.1 i z.2)
        ((cellMeasure d).prod (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
    rw [hU.map_eq]
    exact hf.aestronglyMeasurable
  calc
    _ = ∫ z : PeriodicCell d × UnitAddCircle, f (Function.update z.1 i z.2)
        ∂(cellMeasure d).prod (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
      simpa only [hU.map_eq] using integral_map hU.measurable.aemeasurable hmeas
    _ = _ := integral_prod _ hprod

/-- Proposition 4.7, slicing: the unit circle has the same normalized
integral as one real period. -/
private theorem integral_circle_eq_interval
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : UnitAddCircle → F) :
    (∫ r : UnitAddCircle, f r ∂AddCircle.haarAddCircle) =
      ∫ t in (0 : ℝ)..1, f (t : UnitAddCircle) := by
  rw [AddCircle.integral_haarAddCircle]
  simpa only [inv_one, one_smul, zero_add] using
    (UnitAddCircle.intervalIntegral_preimage 0 f).symm

/-- Proposition 4.7, slicing: coordinate fibres differentiate through the
Euclidean periodic lift, including the seams of the chosen cell. -/
private theorem hasDerivAt_coordinate_fibre
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : PeriodicC1 d F) (j : Fin d) (y : PeriodicCell d) (t : ℝ) :
    HasDerivAt (fun r : ℝ => φ.value (Function.update y j (r : UnitAddCircle)))
      (φ.partial j (Function.update y j (t : UnitAddCircle))) t := by
  let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single j (1 : ℝ))
  have hpath (r : ℝ) :
      toCell (cellRepresentative y + (r - cellRepresentative y j) • v) =
        Function.update y j (r : UnitAddCircle) := by
    funext k
    by_cases hkj : k = j
    · subst k
      change ((cellRepresentative y j + (r - cellRepresentative y j) *
        (Pi.single j (1 : ℝ) : Fin d → ℝ) j : ℝ) : UnitAddCircle) =
        Function.update y j (r : UnitAddCircle) j
      simp only [Pi.single_eq_same, mul_one, Function.update_self]
      congr 1
      ring
    · change ((cellRepresentative y k + (r - cellRepresentative y j) *
        (Pi.single j (1 : ℝ) : Fin d → ℝ) k : ℝ) : UnitAddCircle) =
        Function.update y j (r : UnitAddCircle) k
      simp only [Pi.single_eq_of_ne hkj, mul_zero, add_zero, Function.update_of_ne hkj]
      exact congrFun (toCell_cellRepresentative y) k
  have hc : HasDerivAt
      (fun r : ℝ => cellRepresentative y + (r - cellRepresentative y j) • v) v t := by
    simpa only [one_smul, id_eq] using
      HasDerivAt.const_add (cellRepresentative y)
        (((hasDerivAt_id t).sub_const (cellRepresentative y j)).smul_const v)
  have hl := (φ.contDiff_lift.differentiable one_ne_zero
    (cellRepresentative y + (t - cellRepresentative y j) • v)).hasFDerivAt.comp_hasDerivAt t hc
  have hp := φ.partial_toCell j
    (cellRepresentative y + (t - cellRepresentative y j) • v)
  rw [hpath] at hp
  convert hl using 1
  · funext r
    exact congrArg φ.value (hpath r).symm

/-- Proposition 4.7, slicing: the fundamental theorem of calculus on
each coordinate fibre gives its oriented boundary traces. -/
private theorem integral_coordinate_fibre
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d F) (j : Fin d) (y : PeriodicCell d) (a b : ℝ) :
    (∫ t in a..b, φ.partial j (Function.update y j (t : UnitAddCircle))) =
      φ.value (Function.update y j (b : UnitAddCircle)) -
        φ.value (Function.update y j (a : UnitAddCircle)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_coordinate_fibre φ j y t)
  exact ((φ.continuous_partial j).comp
    (continuous_const.update j (AddCircle.continuous_mk' (1 : ℝ)))).intervalIntegrable a b

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip variation:
integration of a periodic coordinate derivative over an open strip gives
the difference of its two face traces in the normal direction and zero
in every transverse direction. Cell measure is normalized. -/
theorem PeriodicC1.integral_coordinate_strip_partial
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d F) (i j : Fin d) {a : ℝ} (ha : 0 ≤ a) (ha_one : a ≤ 1) :
    (∫ y in {y : PeriodicCell d | 0 < cellRepresentative y i ∧ cellRepresentative y i < a},
      φ.partial j y ∂cellMeasure d) =
      if j = i then
        ∫ y : PeriodicCell d,
          (φ.value (Function.update y i (a : UnitAddCircle)) -
            φ.value (Function.update y i (0 : UnitAddCircle))) ∂cellMeasure d
      else 0 := by
  classical
  let s : Set (PeriodicCell d) :=
    {y | 0 < cellRepresentative y i ∧ cellRepresentative y i < a}
  have hs : MeasurableSet s :=
    (measurePreserving_cellRepresentative_coordinate i).measurable measurableSet_Ioo
  have hf : Integrable (s.indicator (φ.partial j)) (cellMeasure d) :=
    ((φ.continuous_partial j).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).indicator hs
  change (∫ y in s, φ.partial j y ∂cellMeasure d) = _
  rw [← integral_indicator hs, integral_coordinate_update _ hf j]
  by_cases hji : j = i
  · subst j
    rw [ite_eq_left rfl]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    change (∫ r : UnitAddCircle, s.indicator (φ.partial i) (Function.update y i r)
      ∂AddCircle.haarAddCircle) =
        φ.value (Function.update y i (a : UnitAddCircle)) -
          φ.value (Function.update y i (0 : UnitAddCircle))
    let q : ℝ → F := fun t => φ.partial i (Function.update y i (t : UnitAddCircle))
    rw [integral_circle_eq_interval, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    calc
      _ = ∫ r in Set.Ioc (0 : ℝ) 1, (Set.Ioo (0 : ℝ) a).indicator q r := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        have hr' : r ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa only [zero_add] using hr
        have hrep : cellRepresentative (Function.update y i (r : UnitAddCircle)) i = r := by
          change (AddCircle.equivIoc 1 0 (Function.update y i (r : UnitAddCircle) i)).val = r
          rw [Function.update_self, AddCircle.equivIoc_coe_eq hr']
        simp only [Set.indicator, s, Set.mem_ofPred_eq, Set.mem_Ioo, hrep, q]
      _ = ∫ r in Set.Ioo (0 : ℝ) a, q r := by
        rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
          Set.inter_eq_left.mpr (show Set.Ioo (0 : ℝ) a ⊆ Set.Ioc (0 : ℝ) 1 from
            fun r hr => ⟨hr.1, hr.2.le.trans ha_one⟩)]
      _ = ∫ r in (0 : ℝ)..a, q r := by
        rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo]
      _ = _ := integral_coordinate_fibre φ i y 0 a
  · rw [ite_eq_right hji]
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro y
    change (∫ r : UnitAddCircle, s.indicator (φ.partial j) (Function.update y j r)
      ∂AddCircle.haarAddCircle) = 0
    have hmem (r : UnitAddCircle) : Function.update y j r ∈ s ↔ y ∈ s := by
      have hrep : cellRepresentative (Function.update y j r) i = cellRepresentative y i := by
        change (AddCircle.equivIoc 1 0 (Function.update y j r i)).val =
          (AddCircle.equivIoc 1 0 (y i)).val
        rw [Function.update_of_ne (Ne.symm hji)]
      change (0 < cellRepresentative (Function.update y j r) i ∧
        cellRepresentative (Function.update y j r) i < a) ↔ _
      rw [hrep]
      rfl
    by_cases hy : y ∈ s
    · have heq : (fun r : UnitAddCircle => s.indicator (φ.partial j) (Function.update y j r)) =
          fun r : UnitAddCircle => φ.partial j (Function.update y j r) :=
        funext fun r => Set.indicator_of_mem ((hmem r).2 hy) _
      rw [heq, integral_circle_eq_interval, integral_coordinate_fibre]
      simp only [AddCircle.coe_period, AddCircle.coe_zero, sub_self]
    · apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall fun r =>
        Set.indicator_of_notMem (fun h => hy ((hmem r).1 h)) _

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip variation:
the integrated derivative is bounded by the two boundary traces, with
no factor depending on the dimension or strip width. -/
theorem PeriodicC1.norm_integral_coordinate_strip_partial_le
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d F) (i j : Fin d) {a M : ℝ}
    (ha : 0 ≤ a) (ha_one : a ≤ 1) (hφ : ∀ y, ‖φ.value y‖ ≤ M) :
    ‖∫ y in {y : PeriodicCell d | 0 < cellRepresentative y i ∧ cellRepresentative y i < a},
      φ.partial j y ∂cellMeasure d‖ ≤ 2 * M := by
  rw [φ.integral_coordinate_strip_partial i j ha ha_one]
  split_ifs
  · have hc : Continuous (fun y : PeriodicCell d =>
        φ.value (Function.update y i (a : UnitAddCircle)) -
          φ.value (Function.update y i (0 : UnitAddCircle))) :=
      (φ.continuous_value.comp (continuous_id.update i continuous_const)).sub
        (φ.continuous_value.comp (continuous_id.update i continuous_const))
    have hint : Integrable (fun y : PeriodicCell d =>
        φ.value (Function.update y i (a : UnitAddCircle)) -
          φ.value (Function.update y i (0 : UnitAddCircle))) (cellMeasure d) :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      _ ≤ ∫ y : PeriodicCell d,
          ‖φ.value (Function.update y i (a : UnitAddCircle)) -
            φ.value (Function.update y i (0 : UnitAddCircle))‖ ∂cellMeasure d :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ _ : PeriodicCell d, (2 * M) ∂cellMeasure d := by
        apply integral_mono hint.norm (integrable_const _)
        intro y
        exact (norm_sub_le _ _).trans
          ((add_le_add (hφ (Function.update y i (a : UnitAddCircle)))
            (hφ (Function.update y i (0 : UnitAddCircle)))).trans_eq (two_mul M).symm)
      _ = 2 * M := by simp
  · have hM : 0 ≤ M := (norm_nonneg (φ.value (0 : PeriodicCell d))).trans (hφ 0)
    simpa only [norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM

end KVApproximation.Analysis
