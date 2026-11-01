module

public import KVApproximation.Homogenization.CellDisplacement
public import KVApproximation.Dynamics.CellEvolution

/-!
# Physical cell stress and its spatial average
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Dynamics

namespace KVApproximation.Homogenization

/-- Section 3.1: multiplication and addition have their pointwise
representatives outside one spatial null set. -/
private theorem stress_field_apply_ae {d : ℕ} (V E : CoerciveField d)
    (a b : Symmetric d) (u v : StrainField d) :
    multiplication V.field (constantStrainL d a + u) +
      multiplication E.field (constantStrainL d b + v) =ᵐ[cellMeasure d]
        fun y => action (V.field y) (a + u y) + action (E.field y) (b + v y) := by
  filter_upwards
    [Lp.coeFn_add (multiplication V.field (constantStrainL d a + u))
      (multiplication E.field (constantStrainL d b + v)),
      multiplication_apply_ae V.field (constantStrainL d a + u),
      multiplication_apply_ae E.field (constantStrainL d b + v),
      Lp.coeFn_add (constantStrainL d a) u,
      Lp.coeFn_add (constantStrainL d b) v,
      Lp.coeFn_const 2 (cellMeasure d) a,
      Lp.coeFn_const 2 (cellMeasure d) b] with y hsum hV hE hu hv ha hb
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hV, hE, hu, hv]
  simp only [Pi.add_apply]
  change action (V.field y) ((Lp.const 2 (cellMeasure d) a) y + u y) +
    action (E.field y) ((Lp.const 2 (cellMeasure d) b) y + v y) = _
  rw [ha, hb]
  rfl

/-- Section 3.1 (`eq:cell_stress`): the L² stress has the prescribed
pointwise constitutive representative for almost every cell position. -/
theorem periodicCellStress_apply_ae {d : ℕ} (V E : CoerciveField d) {T : ℝ}
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T) (t : ℝ) :
    periodicCellStress (d := d) (T := T) V E e χ t =ᵐ[cellMeasure d] fun y =>
      action (V.field y)
        (TimeH1.velocity (H := Symmetric d) (T := T) e t +
          correctorGradientL d (TimeH1.velocity (H := ZeroMeanPeriodicH1 d) (T := T) χ t) y) +
      action (E.field y)
        (TimeH1.value (H := Symmetric d) (T := T) e t +
          correctorGradientL d (TimeH1.value (H := ZeroMeanPeriodicH1 d) (T := T) χ t) y) :=
  @stress_field_apply_ae d V E
    (TimeH1.velocity (H := Symmetric d) (T := T) e t)
    (TimeH1.value (H := Symmetric d) (T := T) e t)
    (correctorGradientL d (TimeH1.velocity (H := ZeroMeanPeriodicH1 d) (T := T) χ t))
    (correctorGradientL d (TimeH1.value (H := ZeroMeanPeriodicH1 d) (T := T) χ t))

/-- Appendix A.3: on the normalized finite cell, pairing with the spatial
Bochner average is the L² pairing with a constant strain. -/
private theorem inner_spatial_average {d : ℕ} (a : Symmetric d) (f : StrainField d) :
    ⟪a, ∫ y, f y ∂cellMeasure d⟫_ℝ = ⟪constantStrainL d a, f⟫_ℝ := by
  rw [← integral_inner ((Lp.memLp f).integrable (by norm_num)) a, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (cellMeasure d) a] with y hy
  change ⟪a, f y⟫_ℝ = ⟪(Lp.const 2 (cellMeasure d) a) y, f y⟫_ℝ
  rw [hy]
  rfl

/-- Appendix A.3: the symmetric coefficient form agrees with the
unweighted L² pairing against the physical stress. -/
private theorem inner_multiplication {d : ℕ} (A : CoerciveField d)
    (a b : StrainField d) :
    ⟪a, multiplication A.field b⟫_ℝ = A.toForm.form a b := by
  exact (real_inner_comm a (multiplication A.field b)).symm.trans (A.toForm.symmetric b a)

/-- Appendix A.3: averaging the two constitutive terms commutes with testing. -/
private theorem stress_average_pairing {d : ℕ} (V E : CoerciveField d)
    (a b z : Symmetric d) (u v : StrainField d) :
    ⟪z, ∫ y, (multiplication V.field (constantStrainL d a + u) +
        multiplication E.field (constantStrainL d b + v)) y ∂cellMeasure d⟫_ℝ =
      V.toForm.form (constantStrainL d z) (constantStrainL d a + u) +
        E.toForm.form (constantStrainL d z) (constantStrainL d b + v) := by
  rw [inner_spatial_average]
  exact (inner_add_right (𝕜 := ℝ) (constantStrainL d z)
    (multiplication V.field (constantStrainL d a + u))
    (multiplication E.field (constantStrainL d b + v))).trans
      (congrArg₂ (fun x y : ℝ => x + y)
        (inner_multiplication V (constantStrainL d z) (constantStrainL d a + u))
        (inner_multiplication E (constantStrainL d z) (constantStrainL d b + v)))

/-- Appendix A.3, the identity before `eq:stress_decomp`: the spatially
averaged physical stress has the same pairings as the tested cell stress. -/
theorem averagedCellStress_pairing {d : ℕ} (V E : CoerciveField d) {T : ℝ}
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (η : TimeH1 (correctorSubspace d) T)
    (h : IsDisplacementStrain (d := d) (T := T) χ η) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ a : Symmetric d,
      ⟪a, averagedCellStress (d := d) (T := T) V E e χ t⟫_ℝ =
        cellStressPairing (H := StrainField d) (F := Symmetric d)
          V.toForm E.toForm (correctorSubspace d) (constantStrainL d) e η t a := by
  set_option backward.isDefEq.respectTransparency false in
    refine (h.1.and h.2).mono ?_
    intro t ht a
    have hv := ht.1
    have hd := ht.2
    have hav := stress_average_pairing V E
      (TimeH1.velocity (H := Symmetric d) (T := T) e t)
      (TimeH1.value (H := Symmetric d) (T := T) e t) a
      (correctorGradientL d (TimeH1.velocity (H := ZeroMeanPeriodicH1 d) (T := T) χ t))
      (correctorGradientL d (TimeH1.value (H := ZeroMeanPeriodicH1 d) (T := T) χ t))
    exact hav.trans (congrArg₂ (fun u v : StrainField d =>
      V.toForm.form (constantStrainL d a)
        (constantStrainL d (TimeH1.velocity (H := Symmetric d) (T := T) e t) + u) +
      E.toForm.form (constantStrainL d a)
        (constantStrainL d (TimeH1.value (H := Symmetric d) (T := T) e t) + v)) hd.symm hv.symm)

end KVApproximation.Homogenization
