module

public import KVApproximation.Tensor.Fields
public import KVApproximation.Tensor.LinearAction
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Bounded tensor multiplication on strain fields
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Section 3.1: pointwise multiplication by an essentially bounded
coefficient field, as a bounded operator on periodic square-integrable strains. -/
def multiplication {d : ℕ} (A : CoefficientField d ⊤) :
    StrainField d →L[ℝ] StrainField d :=
  (actionL d).holderL (cellMeasure d) ⊤ 2 2 A

/-- Section 3.1: the bounded bilinear energy form obtained from
pointwise tensor multiplication and the unweighted L² inner product. -/
def boundedFieldForm {d : ℕ} (A : CoefficientField d ⊤) :
    StrainField d →L[ℝ] StrainField d →L[ℝ] ℝ :=
  (innerSL ℝ (E := StrainField d)).comp (multiplication A)

end KVApproximation.Tensor
