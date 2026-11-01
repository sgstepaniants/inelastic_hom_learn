module

public import KVApproximation.Analysis.PeriodicSobolev

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Proposition 4.7 (`prop:no_spectral_stability`), corrector construction:
subtracting the mean of a nonconstant periodic displacement preserves its
symmetric gradient and gives a nonzero strain in the zero-mean space. -/
theorem PeriodicC1.exists_zeroMean_nonzero_strain {d : ℕ}
    (φ : PeriodicC1 d (EuclideanSpace ℝ (Fin d)))
    (hnonconstant : ∃ y z, φ.value y ≠ φ.value z) :
    ∃ v : ZeroMeanPeriodicH1 d,
      (PeriodicH1.valueL d (v : PeriodicH1 d) =ᵐ[cellMeasure d]
        fun y => φ.value y - ∫ z, φ.value z ∂cellMeasure d) ∧
      (correctorGradientL d v =ᵐ[cellMeasure d]
        fun y => symmetrizeL d (periodicGradient φ.value y)) ∧
      correctorGradientL d v ≠ 0 := by
  sorry

end KVApproximation.Analysis
