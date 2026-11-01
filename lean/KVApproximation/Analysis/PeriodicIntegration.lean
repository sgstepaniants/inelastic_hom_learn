module

public import KVApproximation.Analysis.PeriodicSmoothIdentities
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Integration of periodic derivatives
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Section 3.1: a derivative of a C¹ periodic field has zero cell average. -/
theorem PeriodicC1.integral_partial_eq_zero {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (φ : PeriodicC1 d F) (j : Fin d) :
    (∫ y, φ.partial j y ∂cellMeasure d) = 0 := by
  let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single j (1 : ℝ))
  let f (t : ℝ) (y : PeriodicCell d) := φ.value (y + toCell (t • v))
  let g (t : ℝ) (y : PeriodicCell d) := φ.partial j (y + toCell (t • v))
  have htranslate (y : PeriodicCell d) (t : ℝ) :
      toCell (cellRepresentative y + t • v) = y + toCell (t • v) := by
    funext i
    change ((cellRepresentative y i + (t • v) i : ℝ) : UnitAddCircle) = _
    rw [AddCircle.coe_add]
    exact congrArg (· + (toCell (t • v)) i)
      (congrFun (toCell_cellRepresentative y) i)
  have hderiv (y : PeriodicCell d) (t : ℝ) :
      HasDerivAt (fun t => f t y) (g t y) t := by
    have hc : HasDerivAt (fun t : ℝ => cellRepresentative y + t • v) v t := by
      simpa only [one_smul, id_eq] using
        HasDerivAt.const_add (cellRepresentative y) ((hasDerivAt_id t).smul_const v)
    have hl := (φ.contDiff_lift.differentiable one_ne_zero
      (cellRepresentative y + t • v)).hasFDerivAt.comp_hasDerivAt t hc
    have hp := φ.partial_toCell j (cellRepresentative y + t • v)
    rw [htranslate] at hp
    convert hl using 1
    · funext s
      exact congrArg φ.value (htranslate y s).symm
  have hf (t : ℝ) : Continuous (f t) :=
    φ.continuous_value.comp (continuous_id.add continuous_const)
  have hg (t : ℝ) : Continuous (g t) :=
    (φ.continuous_partial j).comp (continuous_id.add continuous_const)
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (φ.continuous_partial j).continuousOn
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := cellMeasure d) (F := f) (F' := g) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ => M) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun t => (hf t).aestronglyMeasurable)
    ((hf 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hg 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y t _ => hM _ (Set.mem_univ _))
    (integrable_const M)
    (Filter.Eventually.of_forall fun y t _ => hderiv y t)
  let : (cellMeasure d).IsAddRightInvariant := by
    unfold cellMeasure
    infer_instance
  have hint : (fun t => ∫ y, f t y ∂cellMeasure d) =
      fun _ : ℝ => ∫ y, φ.value y ∂cellMeasure d := by
    funext t
    exact integral_add_right_eq_self φ.value (toCell (t • v))
  rw [hint] at hdiff
  have hz := hdiff.2.unique (hasDerivAt_const (0 : ℝ) _)
  have hzero : toCell (0 : EuclideanSpace ℝ (Fin d)) = 0 := by
    funext i
    change ((0 : ℝ) : UnitAddCircle) = 0
    rfl
  simpa only [g, zero_smul, hzero, add_zero] using hz

/-- Section 3.1: periodic integration by parts for a scalar test and a Banach-valued field. -/
theorem PeriodicC1.integral_smul_partial {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (u : PeriodicC1 d F) (φ : PeriodicC1 d ℝ) (j : Fin d) :
    (∫ y, φ.partial j y • u.value y ∂cellMeasure d) =
      -(∫ y, φ.value y • u.partial j y ∂cellMeasure d) := by
  let ψ : PeriodicC1 d F :=
    ⟨fun y => φ.value y • u.value y, φ.contDiff_lift.smul u.contDiff_lift⟩
  have hpartial (y : PeriodicCell d) : ψ.partial j y =
      φ.value y • u.partial j y + φ.partial j y • u.value y := by
    change (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) =>
      φ.value (toCell x) • u.value (toCell x)) (cellRepresentative y)) _ = _
    rw [fderiv_fun_smul
      (φ.contDiff_lift.differentiable one_ne_zero (cellRepresentative y))
      (u.contDiff_lift.differentiable one_ne_zero (cellRepresentative y))]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, toCell_cellRepresentative]
    rfl
  have h₁ : Integrable (fun y => φ.value y • u.partial j y) (cellMeasure d) :=
    (φ.continuous_value.smul (u.continuous_partial j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h₂ : Integrable (fun y => φ.partial j y • u.value y) (cellMeasure d) :=
    ((φ.continuous_partial j).smul u.continuous_value).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz := ψ.integral_partial_eq_zero j
  simp_rw [hpartial] at hz
  rw [integral_add h₁ h₂] at hz
  exact eq_neg_of_add_eq_zero_right hz

end KVApproximation.Analysis
