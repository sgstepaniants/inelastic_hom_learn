module

public import KVApproximation.Analysis.SobolevDirectionalDerivative
public import TauCeti.Analysis.Sobolev.W1p.Zero

/-!
# Mixed directional derivative identity
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

namespace KVApproximation.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

omit [FiniteDimensional ℝ E] in
/-- Theorem 3.1, spatial coercivity: the directional L² map agrees
almost everywhere with the weak gradient paired with the direction. -/
theorem directionalDerivativeL_apply_ae (a : E) (u : TauCeti.W1p μ Ω 2) :
    ∀ᵐ x ∂μ.restrict (Ω : Set E),
      directionalDerivativeL μ Ω a u x = ⟪a, TauCeti.W1p.gradient u x⟫_ℝ := by
  sorry

/-- Theorem 3.1, Dirichlet Korn argument: integration by parts
interchanges directions in the L² pairing. Only the first scalar
Sobolev function needs zero boundary values. -/
theorem inner_directionalDerivative_swap (u v : TauCeti.W1p μ Ω 2)
    (hu : u ∈ TauCeti.w1p0Submodule μ Ω 2) (a b : E) :
    ⟪directionalDerivativeL μ Ω a u, directionalDerivativeL μ Ω b v⟫_ℝ =
      ⟪directionalDerivativeL μ Ω b u, directionalDerivativeL μ Ω a v⟫_ℝ := by
  sorry

end KVApproximation.Analysis
