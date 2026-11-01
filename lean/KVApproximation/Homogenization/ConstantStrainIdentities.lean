module

public import KVApproximation.Homogenization.CorrectorSpace

/-!
# Norm of a constant strain field
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Section 3.1: normalized cell volume makes the constant-strain embedding isometric. -/
theorem norm_constantStrain {d : ℕ} (e : Symmetric d) :
    ‖constantStrainL d e‖ = ‖e‖ := by
  change ‖Lp.const 2 (cellMeasure d) e‖ = ‖e‖
  rw [Lp.norm_const' 2 (cellMeasure d) e (by norm_num) (by norm_num)]
  simp

end KVApproximation.Homogenization
