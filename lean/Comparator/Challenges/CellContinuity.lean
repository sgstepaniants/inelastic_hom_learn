module

public import KVApproximation.Homogenization.CellOperators

/-!
# Continuity of periodic cell operators
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

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
  sorry

/-- Corollary B.4 (`cor:continuity_tensors`), tensor convergence:
the unique tensor representatives of the static forms converge in Frobenius norm. -/
theorem effective_tensors_converge
    (C : CellConstitutiveModel V E)
    (Cseq : ∀ n, CellConstitutiveModel (Vseq n) (Eseq n)) :
    Tendsto (fun n => (Cseq n).viscosity) atTop (𝓝 C.viscosity) ∧
      Tendsto (fun n => (Cseq n).elasticity) atTop (𝓝 C.elasticity) := by
  sorry

end KVApproximation.Homogenization
