module

public import KVApproximation.Analysis.PeriodicSmooth
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Periodic representatives and continuity
-/

public section

namespace KVApproximation.Analysis

/-- Sections 3.1 and 4.1: the chosen cell representative represents its torus point. -/
theorem toCell_cellRepresentative {d : ℕ} (y : PeriodicCell d) :
    toCell (cellRepresentative y) = y := by
  funext i
  exact AddCircle.coe_equivIoc

/-- Sections 3.1 and 4.1: differentiating the lift is independent of the
cell representative, including at the seams of a fundamental cell. -/
theorem PeriodicC1.partial_toCell {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : PeriodicC1 d F) (j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    φ.partial j (toCell x) =
      fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => φ.value (toCell z)) x
        (WithLp.toLp 2 (Pi.single j (1 : ℝ))) := by
  let a := cellRepresentative (toCell x) - x
  have hshift (z : EuclideanSpace ℝ (Fin d)) : toCell (z + a) = toCell z := by
    funext i
    change ((z i + ((cellRepresentative (toCell x)) i - x i) : ℝ) : UnitAddCircle) =
      (z i : UnitAddCircle)
    rw [AddCircle.coe_add, AddCircle.coe_sub]
    have hx := congrFun (toCell_cellRepresentative (toCell x)) i
    change ((cellRepresentative (toCell x)) i : UnitAddCircle) = (x i : UnitAddCircle) at hx
    rw [hx, sub_self, add_zero]
  have hfun : (fun z : EuclideanSpace ℝ (Fin d) => φ.value (toCell (z + a))) =
      (fun z => φ.value (toCell z)) := funext fun z => congrArg φ.value (hshift z)
  have hfd := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun z : EuclideanSpace ℝ (Fin d) => φ.value (toCell z)) (x := x) a
  rw [hfun] at hfd
  have hxa : x + a = cellRepresentative (toCell x) := by dsimp [a]; abel
  rw [hxa] at hfd
  exact congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] F =>
    L (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) hfd.symm

/-- Sections 3.1 and 4.1: a C¹ periodic lift descends to a continuous field. -/
theorem PeriodicC1.continuous_value {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : PeriodicC1 d F) :
    Continuous φ.value := by
  have hq : IsOpenQuotientMap
      (fun x : Fin d → ℝ => fun i => (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  apply hq.continuous_comp_iff.mp
  exact φ.contDiff_lift.continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

/-- Sections 3.1 and 4.1: coordinate derivatives descend continuously to the torus. -/
theorem PeriodicC1.continuous_partial {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : PeriodicC1 d F) (j : Fin d) : Continuous (φ.partial j) := by
  have hq : IsOpenQuotientMap
      (fun x : Fin d → ℝ => fun i => (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  apply hq.continuous_comp_iff.mp
  have hderiv : Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => φ.value (toCell z)) x
        (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) :=
    (φ.contDiff_lift.continuous_fderiv one_ne_zero).clm_apply continuous_const
  convert hderiv.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)) using 1
  funext x
  exact φ.partial_toCell j (WithLp.toLp 2 x)

end KVApproximation.Analysis
