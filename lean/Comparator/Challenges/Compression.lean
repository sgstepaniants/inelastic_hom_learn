module

public import KVApproximation.Spectral.Compression
public import KVApproximation.Tensor.Trace
public import KVApproximation.OperatorTheory.MemoryKernel

/-!
# Canonical tensor spectral compression
-/

public section

open MeasureTheory
open KVApproximation.OperatorTheory KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Appendix A.2 (`eq:nu_def`): strong PVM additivity and finite-dimensional
tensor representation construct the unique compressed tensor measure. -/
theorem compressedMeasure_exists_unique {d : ℕ} (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (ι : Symmetric d →L[ℝ] H) :
    ∃! ν : TensorMeasure d, IsCompressedMeasure V E X ι ν := by
  sorry

/-- Appendix A.2: compression is positive and its trace is the sum of
the mismatch energies on any orthonormal basis. -/
theorem compressedMeasure_positive_trace {d : ℕ} (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
    (hν : IsCompressedMeasure V E X ι ν) {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis κ ℝ (Symmetric d)) :
    ν.Positive ∧
      tensorTrace (ν Set.univ) = ∑ i, ‖weightedMismatch V E X ι (b i)‖ ^ 2 ∧
      totalVariation ν Set.univ ≤
        ENNReal.ofReal (∑ i, ‖weightedMismatch V E X ι (b i)‖ ^ 2) := by
  sorry

variable {d : ℕ} (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
  (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
  (hν : IsCompressedMeasure V E X ι ν)
  {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
  (hαE : 0 < αE) (hβE : 0 < βE)
  (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE)

include hν hαV hβV hαE hβE hV hE

/-- Appendix A.2: the compressed measure inherits the spectral interval
and is finite in the physical Frobenius norm. -/
theorem compressedMeasure_supported :
    ν.SupportedOn (Set.Icc (αE / βV) (βE / αV)) ∧
      totalVariation ν Set.univ < ⊤ := by
  sorry

/-- Appendix A.2 and Lemma B.5: continuous test functions commute with
compression of the weighted continuous functional calculus. -/
theorem compressedMeasure_integral (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (αE / βV) (βE / αV))) :
    Integrable f ν.variation ∧ ∀ e g : Symmetric d,
      ⟪e, action (tensorIntegral ν f) g⟫_ℝ =
        ⟪cfc f (weightedRelaxation V E X) (weightedMismatch V E X ι e),
          weightedMismatch V E X ι g⟫_ℝ := by
  sorry

/-- Lemma B.5: monomial tests are exactly powers of the original relaxation operator. -/
theorem compressedMeasure_moment (k : ℕ) (e g : Symmetric d) :
    ⟪e, action (tensorIntegral ν (fun r => r ^ k)) g⟫_ℝ =
      V.form ((relaxation V E X ^ k) (mismatch V E X (ι e)))
        (mismatch V E X (ι g)) := by
  sorry

/-- Appendix A.2 (`eq:K_laplace`): the spectral function `r exp(-r t)`
recovers the compressed semigroup kernel. -/
theorem compressedMeasure_memory (t : ℝ) (ht : 0 ≤ t) (e g : Symmetric d) :
    ⟪e, action (tensorIntegral ν (fun r => r * Real.exp (-r * t))) g⟫_ℝ =
      memoryForm V E X ι t e g := by
  sorry

end KVApproximation.Spectral
