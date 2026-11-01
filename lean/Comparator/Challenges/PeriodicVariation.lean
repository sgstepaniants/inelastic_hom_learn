module

public import KVApproximation.Analysis.PeriodicVariation
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Stability of periodic total variation
-/

public section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Section 4.1 (`eq:TV_tensor`): the divergence of a smooth periodic
test field is continuous on the cell. -/
theorem PeriodicC1.continuous_divergence
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F))) :
    Continuous φ.divergence := by
  sorry

/-- Lemma B.2, lower semicontinuity: each distributional variation test
is a continuous scalar functional of the L¹ coefficient field. -/
theorem continuous_periodicTestPairing
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F))) :
    Continuous (fun A : Lp F 1 (cellMeasure d) =>
      ∫ y, ⟪A y, φ.divergence y⟫_ℝ ∂cellMeasure d) := by
  sorry

/-- Section 4.1 (`eq:TV_tensor`): periodic variation depends only on the
almost-everywhere equivalence class. -/
theorem periodicVariation_congr {A B : PeriodicCell d → F}
    (h : A =ᵐ[cellMeasure d] B) : periodicVariation A = periodicVariation B := by
  sorry

/-- Section 4.1 (`eq:bv_bound_microstructure`): the periodic BV norm is
independent of the chosen almost-everywhere representative. -/
theorem periodicBVNorm_congr {A B : PeriodicCell d → F}
    (h : A =ᵐ[cellMeasure d] B) : periodicBVNorm A = periodicBVNorm B := by
  sorry

/-- Lemma B.2 (`lem:bv_compact`), lower semicontinuity: a common BV norm
bound is preserved under L¹ convergence on the periodic cell. -/
theorem periodicBVNorm_le_of_tendsto_L1
    {A : Lp F 1 (cellMeasure d)} {Aseq : ℕ → Lp F 1 (cellMeasure d)} {C : ENNReal}
    (hconv : Tendsto Aseq atTop (𝓝 A))
    (hbound : ∀ n, periodicBVNorm (Aseq n) ≤ C) : periodicBVNorm A ≤ C := by
  sorry

end KVApproximation.Analysis
