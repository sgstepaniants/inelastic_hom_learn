module

public import KVApproximation.Tensor.MultiplicationIdentities

/-!
# Nonnegative combinations of coercive coefficient fields
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Tensor

/-- Theorem 3.1, combined elliptic coefficient: the periodic energy
pairing is linear in the actual L∞ coefficient class. -/
theorem fieldPairing_add_smul {d : ℕ} (A B : CoefficientField d ⊤)
    (c : ℝ) (e f : StrainField d) :
    fieldPairing (A + c • B) e f = fieldPairing A e f + c * fieldPairing B e f := by
  have hp : (fun y => ⟪e y, action ((A + c • B : CoefficientField d ⊤) y) (f y)⟫_ℝ)
      =ᵐ[Analysis.cellMeasure d] fun y =>
        ⟪e y, action (A y) (f y)⟫_ℝ + c * ⟪e y, action (B y) (f y)⟫_ℝ := by
    filter_upwards [Lp.coeFn_add A (c • B), Lp.coeFn_smul c B] with y ha hs
    rw [ha, Pi.add_apply, hs, Pi.smul_apply]
    change ⟪e y, actionL d (A y + c • B y) (f y)⟫_ℝ = _
    simp only [map_add, map_smul, add_apply, smul_apply, actionL_apply, inner_add_right]
    exact congrArg (fun r : ℝ => ⟪e y, action (A y) (f y)⟫_ℝ + r)
      (real_inner_smul_right (e y) (action (B y) (f y)) c)
  unfold fieldPairing
  rw [integral_congr_ae hp,
    integral_add (integrable_fieldPairing A e f) ((integrable_fieldPairing B e f).const_mul c),
    integral_const_mul]

/-- Theorem 3.1, combined elliptic coefficient: nonnegative combinations
retain the corresponding exact lower and upper energy bounds. -/
theorem HasFieldBounds.add_smul {d : ℕ} (A B : CoefficientField d ⊤)
    {αA βA αB βB c : ℝ} (hA : HasFieldBounds αA βA A)
    (hB : HasFieldBounds αB βB B) (hc : 0 ≤ c) :
    HasFieldBounds (αA + c * αB) (βA + c * βB) (A + c • B) := by
  intro e
  rw [fieldPairing_add_smul]
  constructor
  · calc
      (αA + c * αB) * ‖e‖ ^ 2 = αA * ‖e‖ ^ 2 + c * (αB * ‖e‖ ^ 2) := by ring
      _ ≤ fieldPairing A e e + c * fieldPairing B e e :=
        add_le_add (hA e).1 (mul_le_mul_of_nonneg_left (hB e).1 hc)
  · calc
      fieldPairing A e e + c * fieldPairing B e e ≤
          βA * ‖e‖ ^ 2 + c * (βB * ‖e‖ ^ 2) :=
        add_le_add (hA e).2 (mul_le_mul_of_nonneg_left (hB e).2 hc)
      _ = (βA + c * βB) * ‖e‖ ^ 2 := by ring

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`): the actual periodic
coefficient A + c B, with the exact combined coercivity constants.
The Laplace-domain coefficient uses A = V, B = E and c = s⁻¹. -/
@[expose]
def CoerciveField.addSMul {d : ℕ} (A B : CoerciveField d) (c : ℝ)
    (hc : 0 ≤ c) : CoerciveField d where
  field := A.field + c • B.field
  lower := A.lower + c * B.lower
  upper := A.upper + c * B.upper
  lower_pos := add_pos_of_pos_of_nonneg A.lower_pos (mul_nonneg hc B.lower_pos.le)
  bounds := HasFieldBounds.add_smul A.field B.field A.bounds B.bounds hc

end KVApproximation.Tensor
