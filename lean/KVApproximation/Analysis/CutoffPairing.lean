module

public import KVApproximation.Tensor.OuterProduct
public import TauCeti.Analysis.Sobolev.TestFunctionLp
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Localized stress and displacement pairings

The bounded cutoff gradient multiplies L² displacements through
Hölder's inequality. Its L² Frobenius pairing acts continuously on both
the stress and displacement fields.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped Distributions

namespace KVApproximation.Analysis

/-- Theorem 3.1, localized test gradients: the term u ⊗ ∇χ is a
bounded linear map from displacement L² to full-gradient L². -/
def cutoffGradientL {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin d))} (χ : 𝓓(Ω, ℝ)) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) →L[ℝ]
      Lp (SecondOrder d) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) :=
  (outerL d).flip.holderL (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) ⊤ 2 2
    (TauCeti.gradientTestFunctionLp (mu := volume) ⊤ χ)

/-- Theorem 3.1, localized flux limits: the stress paired with the
cutoff-gradient term, as a continuous bilinear form on the two L² fields. -/
def cutoffPairing {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin d))} (χ : 𝓓(Ω, ℝ)) :
    Lp (Symmetric d) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))) →L[ℝ] ℝ :=
  let μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin d)))
  ((ContinuousLinearMap.compL ℝ (Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
    (Lp (SecondOrder d) 2 μ) ℝ).flip (cutoffGradientL χ)).comp
      ((innerSL ℝ (E := Lp (SecondOrder d) 2 μ)).comp
        ((symmetricSubmodule d).subtypeL.compLpL 2 μ))

end KVApproximation.Analysis
