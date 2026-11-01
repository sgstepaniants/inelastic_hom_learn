module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Smooth multiplication on Sobolev jets

The value and gradient of a scalar cutoff act through the L∞–L²
Hölder maps. The resulting bounded operator records the product rule.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal

namespace KVApproximation.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- Theorem 3.1, compactly supported oscillating tests: multiplication
by a scalar test function on the ambient value-gradient L² space,
including the gradient product rule. -/
def cutoffJetL (χ : 𝓓(Ω, ℝ)) :
    TauCeti.Sobolev1JetLp μ Ω 2 →L[ℝ] TauCeti.Sobolev1JetLp μ Ω 2 :=
  let ν := μ.restrict (Ω : Set E)
  let a := TauCeti.testFunctionLp (mu := μ) ⊤ χ
  let b := TauCeti.gradientTestFunctionLp (mu := μ) ⊤ χ
  let V := ((ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holderL ν ⊤ 2 2 a).comp
    TauCeti.Sobolev1JetLp.valueL
  let G := ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL ν ⊤ 2 2 a).comp
      TauCeti.Sobolev1JetLp.gradientL +
    (((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip).holderL ν ⊤ 2 2 b).comp
      TauCeti.Sobolev1JetLp.valueL
  let I₀ := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ ℝ E)
  let I₁ := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ ℝ E)
  (I₀.compLpL 2 ν).comp V + (I₁.compLpL 2 ν).comp G

end KVApproximation.Analysis
