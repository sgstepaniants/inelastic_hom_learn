module

public import KVApproximation.Spectral.TensorMeasure
public import KVApproximation.Tensor.Trace
public import ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

/-!
# Finite-dimensional compression of a projection-valued measure
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance pvmCompressionRealInnerProduct : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- Appendix A.2 (`eq:nu_def`): finite-dimensional compression of a general PVM
is a unique countably additive tensor measure. -/
theorem pvmCompression_exists_unique {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) :
    ∃! ν : TensorMeasure d, ∀ (B : Set ℝ) (hB : MeasurableSet B) (e f : Symmetric d),
      ⟪e, action (ν B) f⟫_ℝ = (⟪P.proj B hB (L e), L f⟫_ℂ).re := by
  sorry

/-- Appendix A.2: the compressed PVM is positive; its total trace and
Frobenius variation are controlled by the compression energies. -/
theorem pvmCompression_positive_trace {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
    (hν : ∀ (B : Set ℝ) (hB : MeasurableSet B) (e f : Symmetric d),
      ⟪e, action (ν B) f⟫_ℝ = (⟪P.proj B hB (L e), L f⟫_ℂ).re)
    {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ (Symmetric d)) :
    ν.Positive ∧ tensorTrace (ν Set.univ) = ∑ i, ‖L (b i)‖ ^ 2 ∧
      totalVariation ν Set.univ ≤ ENNReal.ofReal (∑ i, ‖L (b i)‖ ^ 2) := by
  sorry

/-- Appendix A.2: integrable diagonal tensor tests equal the positive scalar
spectral integral. Mixed tests are recovered by real polarization. -/
theorem pvmCompression_integral_diag {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d → H) (ν : TensorMeasure d)
    (hν : ∀ (B : Set ℝ) (hB : MeasurableSet B) (e g : Symmetric d),
      ⟪e, action (ν B) g⟫_ℝ = (⟪P.proj B hB (L e), L g⟫_ℂ).re)
    (f : ℝ → ℝ) (e : Symmetric d)
    (hνf : Integrable f ν.variation) (hPf : Integrable f (P.diag (L e))) :
    ⟪e, action (tensorIntegral ν f) e⟫_ℝ = ∫ r, f r ∂P.diag (L e) := by
  sorry

end KVApproximation.Spectral
