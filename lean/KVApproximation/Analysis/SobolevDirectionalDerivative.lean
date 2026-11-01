module

public import TauCeti.Analysis.Sobolev.W1p.Basic

/-!
# Directional weak derivatives in L²
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace KVApproximation.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Theorem 3.1, spatial coercivity: the directional weak derivative
as a bounded linear map into the scalar L² space. -/
def directionalDerivativeL (μ : Measure E) [μ.IsAddHaarMeasure]
    (Ω : Opens E) (a : E) :
    TauCeti.W1p μ Ω 2 →L[ℝ] Lp ℝ 2 (μ.restrict (Ω : Set E)) :=
  ((innerSL ℝ a).compLpL 2 (μ.restrict (Ω : Set E))).comp TauCeti.W1p.gradientL

end KVApproximation.Analysis
