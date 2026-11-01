module

public import KVApproximation.Homogenization.CorrectorSpace
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Displacement recovery from a periodic strain corrector
-/

public section

open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Section 3.1 and Appendix A.3: a zero-mean periodic displacement is
uniquely determined by its symmetric gradient. -/
theorem correctorGradient_injective (d : ℕ) :
    Function.Injective (correctorGradientL d) := by
  sorry

/-- Section 3.1 (`eq:space_strain_corrector`) and Appendix A.3: the symmetric
gradient identifies the displacement and strain corrector spaces. The inverse
retains the full periodic H¹ bound from Korn's inequality. -/
theorem correctorGradient_equiv_exists (d : ℕ) :
    ∃ L : ZeroMeanPeriodicH1 d ≃L[ℝ] (correctorSubspace d).toSubmodule,
      (∀ u : ZeroMeanPeriodicH1 d, (L u : StrainField d) = correctorGradientL d u) ∧
      ∀ η : (correctorSubspace d).toSubmodule, ‖L.symm η‖ ≤ 2 * ‖η‖ := by
  sorry

end KVApproximation.Homogenization
