module

public import KVApproximation.Analysis.PeriodicCell
public import KVApproximation.Tensor.Action

/-!
# Periodic tensor fields and their energy forms
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Section 3.1: square-integrable symmetric strain fields on the unit cell. -/
abbrev StrainField (d : ℕ) := Lp (Symmetric d) 2 (cellMeasure d)

/-- Section 4.1 (`eq:admissible_microstructure`): tensor coefficient fields
with a specified integrability exponent. -/
abbrev CoefficientField (d : ℕ) (p : ENNReal) :=
  Lp (Elasticity d) p (cellMeasure d)

/-- Section 3.1: the coefficient-weighted pairing before imposing
boundedness and coercivity. Its applications use essentially bounded fields. -/
def fieldPairing {d : ℕ} (A : PeriodicCell d → Elasticity d)
    (e f : StrainField d) : ℝ :=
  ∫ y, ⟪e y, action (A y) (f y)⟫_ℝ ∂cellMeasure d

/-- Proposition 3.3 (`eq:constants_spectral_rep`): integrated ellipticity
and boundedness on the full periodic strain space. -/
def HasFieldBounds {d : ℕ} (α β : ℝ) (A : PeriodicCell d → Elasticity d) : Prop :=
  ∀ e : StrainField d,
    α * ‖e‖ ^ 2 ≤ fieldPairing A e e ∧ fieldPairing A e e ≤ β * ‖e‖ ^ 2

/-- Section 3.1: an essentially bounded, uniformly coercive periodic
coefficient field. The upper quadratic-form bound is retained explicitly. -/
structure CoerciveField (d : ℕ) where
  field : CoefficientField d ⊤
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  bounds : HasFieldBounds lower upper field

end KVApproximation.Tensor
