module

public import KVApproximation.Analysis.PeriodicSmooth

/-!
# Variation of a field on the periodic cell
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Section 4.1 (`eq:TV_tensor`): divergence of an `F ⊗ ℝᵈ` test field.
The fibre uses the Euclidean sum of the component norms. -/
def PeriodicC1.divergence {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F))) (y : PeriodicCell d) : F :=
  ∑ i : Fin d, (φ.partial i y) i

/-- Section 4.1 (`eq:TV_tensor`): the dual total-variation seminorm,
including the value infinity when the field does not have bounded variation. -/
def periodicVariation {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : PeriodicCell d → F) : ENNReal :=
  ⨆ (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F)))
    (_hφ : ∀ y, ‖φ.value y‖ ≤ 1),
      ENNReal.ofReal (∫ y, ⟪A y, φ.divergence y⟫_ℝ ∂cellMeasure d)

/-- Section 4.1 (`eq:bv_bound_microstructure`): the sum of the L¹ norm
and the dual variation seminorm. -/
def periodicBVNorm {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : PeriodicCell d → F) : ENNReal :=
  eLpNorm A 1 (cellMeasure d) + periodicVariation A

end KVApproximation.Analysis
