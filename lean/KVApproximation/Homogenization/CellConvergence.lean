module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.OperatorTheory.FieldFormIdentities
public import KVApproximation.OperatorTheory.VariationalStability
public import KVApproximation.Tensor.FieldNormBounds
public import KVApproximation.Analysis.MultiplicationConvergence

/-!
# Strong convergence of periodic cell operators

Proposition B.3 applies the energy estimates to the strongly convergent
coefficient multipliers. The common relaxation bound then permits induction
on the operator powers.
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory

namespace KVApproximation.Homogenization

private theorem tendsto_of_norm_sub_le {F : Type*} [NormedAddCommGroup F]
    {f : ℕ → F} {a : F} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (h : ∀ n, ‖f n - a‖ ≤ r n) :
    Tendsto f atTop (𝓝 a) :=
  tendsto_iff_norm_sub_tendsto_zero.2
    (tendsto_const_nhds.squeeze hr (fun n => norm_nonneg (f n - a)) h)

private theorem riesz_apply_eq_multiplication {d : ℕ} (A : CoerciveField d)
    (e : StrainField d) : A.toForm.riesz e = multiplication A.field e :=
  congrArg (fun L : StrainField d →L[ℝ] StrainField d => L e) A.riesz_eq_multiplication

private theorem riesz_tendsto {d : ℕ} {α β : ℝ}
    (A : CoerciveField d) (Aseq : ℕ → CoerciveField d)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hseq : ∀ n, HasFieldBounds α β (Aseq n).field)
    (hconv : Tendsto
      (fun n => eLpNorm (fun y => (Aseq n).field y - A.field y) 1 (cellMeasure d))
        atTop (𝓝 0)) (e : StrainField d) :
    Tendsto (fun n => (Aseq n).toForm.riesz e) atTop (𝓝 (A.toForm.riesz e)) := by
  simp only [riesz_apply_eq_multiplication]
  apply multiplication_strong_tendsto A.field (fun n => (Aseq n).field)
    (κ := Real.sqrt (strainDimension d) * β) (mul_nonneg (Real.sqrt_nonneg _) hβ)
  · intro n
    exact HasFieldBounds.eLpNorm_top_le (Aseq n).field hα hβ (hseq n)
  · exact hconv

private theorem projection_tendsto {d : ℕ} {α β : ℝ}
    (A : CoerciveField d) (Aseq : ℕ → CoerciveField d)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hseq : ∀ n, HasFieldBounds α β (Aseq n).field)
    (hconv : Tendsto
      (fun n => eLpNorm (fun y => (Aseq n).field y - A.field y) 1 (cellMeasure d))
        atTop (𝓝 0)) (e : StrainField d) :
    Tendsto (fun n => cellProjection (Aseq n) e) atTop (𝓝 (cellProjection A e)) := by
  let : NormedAddCommGroup (correctorSubspace d) :=
    inferInstanceAs (NormedAddCommGroup (correctorSubspace d).toSubmodule)
  have h := tendsto_iff_norm_sub_tendsto_zero.1
    (riesz_tendsto A Aseq hα.le hβ hseq hconv
      (A.toForm.complement (correctorSubspace d) e))
  apply tendsto_of_norm_sub_le (F := correctorSubspace d)
    (r := fun n => ‖(Aseq n).toForm.riesz (A.toForm.complement (correctorSubspace d) e) -
      A.toForm.riesz (A.toForm.complement (correctorSubspace d) e)‖ / α)
  · simpa only [zero_div] using h.div_const α
  · intro n
    apply projection_sub_norm_le (Aseq n).toForm A.toForm (correctorSubspace d) hα
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using (hseq n u).1

private theorem tendsto_apply_of_uniform_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : F →L[ℝ] F) (Tseq : ℕ → F →L[ℝ] F) {C : ℝ}
    (hbound : ∀ n, ‖Tseq n‖ ≤ C)
    (hT : ∀ x, Tendsto (fun n => Tseq n x) atTop (𝓝 (T x)))
    {x : F} {xs : ℕ → F} (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n => Tseq n (xs n)) atTop (𝓝 (T x)) := by
  have h₁ := (tendsto_iff_norm_sub_tendsto_zero.1 hx).const_mul C
  have h₂ := tendsto_iff_norm_sub_tendsto_zero.1 (hT x)
  apply tendsto_of_norm_sub_le
    (r := fun n => C * ‖xs n - x‖ + ‖Tseq n x - T x‖)
  · simpa only [mul_zero, zero_add] using h₁.add h₂
  · intro n
    calc
      ‖Tseq n (xs n) - T x‖ = ‖Tseq n (xs n - x) + (Tseq n x - T x)‖ := by
        rw [map_sub, sub_add_sub_cancel]
      _ ≤ ‖Tseq n (xs n - x)‖ + ‖Tseq n x - T x‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_left
        (((Tseq n).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))) _

private theorem effective_form_tendsto {d : ℕ}
    (A : CoerciveField d) (Aseq : ℕ → CoerciveField d)
    (hA : ∀ u : StrainField d,
      Tendsto (fun n => (Aseq n).toForm.riesz u) atTop (𝓝 (A.toForm.riesz u)))
    (hP : ∀ u : StrainField d,
      Tendsto (fun n => cellProjection (Aseq n) u) atTop (𝓝 (cellProjection A u)))
    (e f : Symmetric d) :
    Tendsto (fun n => effectiveForm (Aseq n) e f) atTop (𝓝 (effectiveForm A e f)) := by
  have hc : Tendsto
      (fun n => (Aseq n).toForm.complement (correctorSubspace d) (constantStrainL d f))
      atTop (𝓝 (A.toForm.complement (correctorSubspace d) (constantStrainL d f))) := by
    change Tendsto
      (fun n => constantStrainL d f - (cellProjection (Aseq n) (constantStrainL d f) : StrainField d))
      atTop (𝓝 (constantStrainL d f - (cellProjection A (constantStrainL d f) : StrainField d)))
    exact tendsto_const_nhds.sub
      ((continuous_subtype_val.tendsto _).comp (hP (constantStrainL d f)))
  have h := (hA (constantStrainL d e)).inner (𝕜 := ℝ) hc
  change Tendsto
    (fun n => (Aseq n).toForm.form (constantStrainL d e)
      ((Aseq n).toForm.complement (correctorSubspace d) (constantStrainL d f)))
    atTop (𝓝 (A.toForm.form (constantStrainL d e)
      (A.toForm.complement (correctorSubspace d) (constantStrainL d f))))
  simpa only [CoerciveForm.riesz_spec] using h

variable {d : ℕ} {αV βV αE βE : ℝ}
variable (V E : CoerciveField d) (Vseq Eseq : ℕ → CoerciveField d)
variable (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
variable (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field)
variable (hVseq : ∀ n, HasFieldBounds αV βV (Vseq n).field)
variable (hEseq : ∀ n, HasFieldBounds αE βE (Eseq n).field)
variable (hVconv : Tendsto
  (fun n => eLpNorm (fun y => (Vseq n).field y - V.field y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (hEconv : Tendsto
  (fun n => eLpNorm (fun y => (Eseq n).field y - E.field y) 1 (cellMeasure d)) atTop (𝓝 0))

include hαV hβV hαE hβE hV hE hVseq hEseq hVconv hEconv

set_option linter.unusedSectionVars false in
/-- Proposition B.3 (`prop:strong_conv`), operator convergence:
the two projections, their mismatch, and every power of the relaxation
operator converge strongly under uniform bounds and L¹ coefficient convergence.
Lemma B.2 supplies admissibility of a material-class limit in the paper specialization. -/
theorem cell_operators_converge :
    (∀ e : StrainField d,
      Tendsto (fun n => cellProjection (Vseq n) e) atTop (𝓝 (cellProjection V e))) ∧
    (∀ e : StrainField d,
      Tendsto (fun n => cellProjection (Eseq n) e) atTop (𝓝 (cellProjection E e))) ∧
    (∀ e : StrainField d,
      Tendsto (fun n => cellMismatch (Vseq n) (Eseq n) e)
        atTop (𝓝 (cellMismatch V E e))) ∧
    (∀ η : correctorSubspace d,
      Tendsto (fun n => cellRelaxation (Vseq n) (Eseq n) η)
        atTop (𝓝 (cellRelaxation V E η))) ∧
    ∀ (k : ℕ) (η : correctorSubspace d),
      Tendsto (fun n => (cellRelaxation (Vseq n) (Eseq n) ^ k) η)
        atTop (𝓝 ((cellRelaxation V E ^ k) η)) := by
  let : NormedAddCommGroup (correctorSubspace d) :=
    inferInstanceAs (NormedAddCommGroup (correctorSubspace d).toSubmodule)
  let : NormedSpace ℝ (correctorSubspace d) :=
    inferInstanceAs (NormedSpace ℝ (correctorSubspace d).toSubmodule)
  have hPV := projection_tendsto V Vseq hαV hβV.le hVseq hVconv
  have hPE := projection_tendsto E Eseq hαE hβE.le hEseq hEconv
  have hR : ∀ η : correctorSubspace d,
      Tendsto (fun n => cellRelaxation (Vseq n) (Eseq n) η)
        atTop (𝓝 (cellRelaxation V E η)) := by
    intro η
    have h₁ := tendsto_iff_norm_sub_tendsto_zero.1
      (riesz_tendsto E Eseq hαE.le hβE.le hEseq hEconv η)
    have h₂ := tendsto_iff_norm_sub_tendsto_zero.1
      (riesz_tendsto V Vseq hαV.le hβV.le hVseq hVconv (cellRelaxation V E η))
    apply tendsto_of_norm_sub_le (F := correctorSubspace d)
      (r := fun n => (‖(Eseq n).toForm.riesz (η : StrainField d) - E.toForm.riesz η‖ +
        ‖(Vseq n).toForm.riesz (cellRelaxation V E η : StrainField d) -
          V.toForm.riesz (cellRelaxation V E η)‖) / αV)
    · simpa only [zero_add, zero_div] using (h₁.add h₂).div_const αV
    · intro n
      apply relaxation_sub_norm_le (Vseq n).toForm (Eseq n).toForm
        V.toForm E.toForm (correctorSubspace d) hαV
      intro u
      simpa only [CoerciveField.toForm, boundedFieldForm_apply] using (hVseq n u).1
  have hnorm (n : ℕ) : ‖cellRelaxation (Vseq n) (Eseq n)‖ ≤ βE / αV := by
    apply relaxation_opNorm_le (Vseq n).toForm (Eseq n).toForm
      (correctorSubspace d) hαV hβE.le
    · intro u
      simpa only [CoerciveField.toForm, boundedFieldForm_apply] using (hVseq n u).1
    · intro u
      simpa only [CoerciveField.toForm, boundedFieldForm_apply] using (hEseq n u).2
  refine ⟨hPV, hPE, ?_, hR, ?_⟩
  · intro e
    exact (hPV e).sub (hPE e)
  · intro k
    induction k with
    | zero =>
      intro η
      simpa only [pow_zero, one_apply_eq_self] using tendsto_const_nhds
    | succ k hk =>
      intro η
      have h := tendsto_apply_of_uniform_bound (F := correctorSubspace d)
        (cellRelaxation (d := d) V E)
        (fun n => cellRelaxation (d := d) (Vseq n) (Eseq n)) hnorm hR (hk η)
      simpa only [pow_succ', mul_apply_eq_comp] using h

/-- Corollary B.4 (`cor:continuity_tensors`), tensor convergence:
the unique tensor representatives of the static forms converge in Frobenius norm. -/
theorem effective_tensors_converge
    (C : CellConstitutiveModel V E)
    (Cseq : ∀ n, CellConstitutiveModel (Vseq n) (Eseq n)) :
    Tendsto (fun n => (Cseq n).viscosity) atTop (𝓝 C.viscosity) ∧
      Tendsto (fun n => (Cseq n).elasticity) atTop (𝓝 C.elasticity) := by
  have hcell := cell_operators_converge V E Vseq Eseq hαV hβV hαE hβE
    hV hE hVseq hEseq hVconv hEconv
  constructor
  · apply tendsto_of_inner_action
    intro e f
    simp only [(Cseq _).viscosity_eq, C.viscosity_eq]
    exact effective_form_tendsto V Vseq
      (riesz_tendsto V Vseq hαV.le hβV.le hVseq hVconv) hcell.1 e f
  · apply tendsto_of_inner_action
    intro e f
    simp only [(Cseq _).elasticity_eq, C.elasticity_eq]
    exact effective_form_tendsto E Eseq
      (riesz_tendsto E Eseq hαE.le hβE.le hEseq hEconv) hcell.2.1 e f

end KVApproximation.Homogenization
