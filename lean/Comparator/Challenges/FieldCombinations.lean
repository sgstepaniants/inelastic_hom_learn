module

public import KVApproximation.Tensor.MultiplicationIdentities

public section

namespace KVApproximation.Tensor

/-- Theorem 3.1, combined elliptic coefficient: the periodic energy
pairing is linear in the actual L∞ coefficient class. -/
theorem fieldPairing_add_smul {d : ℕ} (A B : CoefficientField d ⊤)
    (c : ℝ) (e f : StrainField d) :
    fieldPairing (A + c • B) e f = fieldPairing A e f + c * fieldPairing B e f := by
  sorry

/-- Theorem 3.1, combined elliptic coefficient: nonnegative combinations
retain the corresponding exact lower and upper energy bounds. -/
theorem HasFieldBounds.add_smul {d : ℕ} (A B : CoefficientField d ⊤)
    {αA βA αB βB c : ℝ} (hA : HasFieldBounds αA βA A)
    (hB : HasFieldBounds αB βB B) (hc : 0 ≤ c) :
    HasFieldBounds (αA + c * αB) (βA + c * βB) (A + c • B) := by
  sorry

end KVApproximation.Tensor
