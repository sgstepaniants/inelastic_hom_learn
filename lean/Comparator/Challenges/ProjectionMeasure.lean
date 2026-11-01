module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Strong additivity and continuous spectral integration
-/

public section

open MeasureTheory
open scoped InnerProductSpace

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Appendix A.2: countable additivity of a PVM holds after applying it to
each vector, without an operator-norm additivity or compactness assumption. -/
theorem projectionMeasure_hasSum (P : TauCeti.ProjValMeasure H)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (u : H) :
    HasSum (fun n => P.proj (B n) (hB n) u)
      (P.proj (⋃ n, B n) (MeasurableSet.iUnion hB) u) := by
  sorry

/-- Appendix A.2: a common spectral interval supports the canonical bounded PVM. -/
theorem boundedPVM_supported {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) {a b : ℝ}
    (hI : ∀ z ∈ spectrum ℂ R, z.re ∈ Set.Icc a b) :
    (TauCeti.BorelCalculus.boundedPVM hR).proj (Set.Icc a b) measurableSet_Icc =
        ContinuousLinearMap.id ℂ H ∧
      (TauCeti.BorelCalculus.boundedPVM hR).proj (Set.Icc a b)ᶜ measurableSet_Icc.compl = 0 := by
  sorry

/-- Appendix A.2 and Lemma B.5: continuous spectral tests agree with the
functional calculus through the finite scalar diagonal measures. -/
theorem boundedPVM_integral {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) {a b : ℝ}
    (hI : ∀ z ∈ spectrum ℂ R, z.re ∈ Set.Icc a b)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (u : H) :
    Integrable f ((TauCeti.BorelCalculus.boundedPVM hR).diag u) ∧
      (∫ r, f r ∂(TauCeti.BorelCalculus.boundedPVM hR).diag u) =
        (⟪u, cfc f R u⟫_ℂ).re := by
  sorry

end KVApproximation.Spectral
