module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Finite Euclidean coordinates in L²
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Theorem 3.1, spatial Sobolev foundations: assembling finitely many L²
fields preserves the Euclidean sum of their squared norms. This is valid
for arbitrary measures and includes an empty coordinate type. -/
theorem lp_finite_coordinates {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (μ : Measure X) :
    ∃ U : PiLp 2 (fun i => Lp (E i) 2 μ) ≃ₗᵢ[ℝ] Lp (PiLp 2 E) 2 μ,
      ∀ f : PiLp 2 (fun i => Lp (E i) 2 μ),
        ∀ᵐ x ∂μ, U f x = WithLp.toLp 2 (fun i => f i x) := by
  sorry

end KVApproximation.Analysis
