module

public import KVApproximation.Tensor.Multiplication
public import KVApproximation.Tensor.LinearActionIdentities

/-!
# Energy pairings of bounded coefficient fields
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Section 3.1: changing coefficient representatives on a null set
does not change the energy form. -/
theorem fieldPairing_congr {d : ℕ} {A B : PeriodicCell d → Elasticity d}
    (hAB : A =ᵐ[cellMeasure d] B) (e f : StrainField d) :
    fieldPairing A e f = fieldPairing B e f := by
  apply integral_congr_ae
  filter_upwards [hAB] with y hy
  rw [hy]

/-- Section 3.1: integrated coefficient bounds are properties of the
almost-everywhere class. -/
theorem HasFieldBounds.congr {d : ℕ} {A B : PeriodicCell d → Elasticity d}
    {α β : ℝ} (hA : HasFieldBounds α β A) (hAB : A =ᵐ[cellMeasure d] B) :
    HasFieldBounds α β B := by
  intro e
  rw [← fieldPairing_congr hAB]
  exact hA e

/-- Sections 3.1 and 4.1: an essentially bounded representative with
the prescribed energy bounds determines a coercive coefficient field. -/
@[expose]
noncomputable def CoerciveField.ofMemLp {d : ℕ} (A : PeriodicCell d → Elasticity d)
    (hA : MemLp A ⊤ (cellMeasure d))
    (α β : ℝ) (hα : 0 < α) (hbounds : HasFieldBounds α β A) : CoerciveField d where
  field := hA.toLp A
  lower := α
  upper := β
  lower_pos := hα
  bounds := hbounds.congr hA.coeFn_toLp.symm

/-- Section 3.1: the bounded multiplication operator represents pointwise contraction. -/
theorem multiplication_apply_ae {d : ℕ} (A : CoefficientField d ⊤)
    (e : StrainField d) :
    multiplication A e =ᵐ[cellMeasure d] fun y => action (A y) (e y) := by
  exact (actionL d).coeFn_holder A e

/-- Section 3.1: the energy integrand is integrable for bounded coefficients. -/
theorem integrable_fieldPairing {d : ℕ} (A : CoefficientField d ⊤)
    (e f : StrainField d) :
    Integrable (fun y => ⟪e y, action (A y) (f y)⟫_ℝ) (cellMeasure d) := by
  apply (L2.integrable_inner (𝕜 := ℝ) e (multiplication A f)).congr
  filter_upwards [multiplication_apply_ae A f] with y hy
  rw [hy]

/-- Section 3.1: the constructed bounded form equals the paper's coefficient-weighted pairing. -/
theorem boundedFieldForm_apply {d : ℕ} (A : CoefficientField d ⊤)
    (e f : StrainField d) :
    boundedFieldForm A e f = fieldPairing A e f := by
  change ⟪multiplication A e, f⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplication_apply_ae A e] with y hy
  rw [hy, action_symmetric]

/-- Section 3.1: symmetry of the coefficient-weighted L² form. -/
theorem boundedFieldForm_symmetric {d : ℕ} (A : CoefficientField d ⊤)
    (e f : StrainField d) :
    boundedFieldForm A e f = boundedFieldForm A f e := by
  rw [boundedFieldForm_apply, boundedFieldForm_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y =>
    (action_symmetric (A y) (e y) (f y)).symm.trans (real_inner_comm _ _)

end KVApproximation.Tensor
