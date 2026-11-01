module

public import KVApproximation.Homogenization.CorrectorSpace
public import KVApproximation.Analysis.PeriodicKorn
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Closed range of the periodic symmetric gradient
-/

public section

open KVApproximation.Analysis
open scoped NNReal

namespace KVApproximation.Homogenization

private theorem closed_range_of_two_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (h : ∀ u, ‖u‖ ≤ 2 * ‖L u‖) :
    L.range.topologicalClosure = L.range := by
  exact ContinuousLinearMap.closed_range_of_antilipschitz
    (L.antilipschitz_of_bound (K := (2 : ℝ≥0)) h)

/-- Section 3.1 (`eq:space_strain_corrector`): Korn's inequality makes
the concrete strain-corrector range closed. -/
theorem correctorSubspace_eq_range (d : ℕ) :
    (correctorSubspace d).toSubmodule =
      LinearMap.range (correctorGradientL d).toLinearMap := by
  change (correctorGradientL d).range.topologicalClosure = (correctorGradientL d).range
  apply closed_range_of_two_bound (E := ZeroMeanPeriodicH1 d) (F := Tensor.StrainField d)
    (correctorGradientL d)
  intro u
  exact periodic_korn_two (d := d) u

end KVApproximation.Homogenization
