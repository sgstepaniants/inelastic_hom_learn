module

public import KVApproximation.Analysis.SobolevCutoffMap

public section

open MeasureTheory TopologicalSpace
open scoped Distributions Gradient

namespace KVApproximation.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- Theorem 3.1, cutoff product rule: the bounded jet operator has the
pointwise value and full-gradient formula almost everywhere. -/
theorem cutoffJetL_apply_ae (χ : 𝓓(Ω, ℝ)) (J : TauCeti.Sobolev1JetLp μ Ω 2) :
    cutoffJetL χ J =ᵐ[μ.restrict (Ω : Set E)] fun x =>
      WithLp.toLp 2 (χ x * WithLp.fst (J x),
        χ x • WithLp.snd (J x) + WithLp.fst (J x) • ∇ (χ : E → ℝ) x) := by
  sorry

/-- Theorem 3.1, compactly supported tests: a cutoff of a smooth jet
is represented by an actual zero-boundary Sobolev function. -/
theorem cutoffJetL_mem_of_smooth (χ : 𝓓(Ω, ℝ))
    (J : TauCeti.Sobolev1JetLp μ Ω 2) {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hv : TauCeti.Sobolev1JetLp.value J =ᵐ[μ.restrict (Ω : Set E)] f)
    (hg : TauCeti.Sobolev1JetLp.gradient J =ᵐ[μ.restrict (Ω : Set E)] ∇ f) :
    cutoffJetL χ J ∈ Subtype.val ''
      (TauCeti.w1p0Submodule μ Ω 2 : Set (TauCeti.W1p μ Ω 2)) := by
  sorry

/-- Theorem 3.1, localized weak tests: smooth cutoff multiplication
preserves the zero-boundary Sobolev space on any open domain. -/
theorem cutoffJetL_mem_of_zeroBoundary (χ : 𝓓(Ω, ℝ)) (u : TauCeti.W1p μ Ω 2)
    (hu : u ∈ TauCeti.w1p0Submodule μ Ω 2) :
    cutoffJetL χ (u : TauCeti.Sobolev1JetLp μ Ω 2) ∈ Subtype.val ''
      (TauCeti.w1p0Submodule μ Ω 2 : Set (TauCeti.W1p μ Ω 2)) := by
  sorry

end KVApproximation.Analysis
