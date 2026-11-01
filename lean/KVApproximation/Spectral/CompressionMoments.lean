module

public import KVApproximation.Spectral.CompressionIntegration
public import KVApproximation.OperatorTheory.MemoryIdentities
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Moments and the memory representation

Polynomial tests give the powers used in Lemma B.5. The spectral function
`r exp(-r t)` gives the memory formula in Appendix A.2.
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.OperatorTheory KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {d : ℕ} (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
  (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
  (hν : IsCompressedMeasure V E X ι ν)
  {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
  (hαE : 0 < αE) (hβE : 0 < βE)
  (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE)

include hν hαV hβV hαE hβE hV hE

/-- Lemma B.5: monomial tests are exactly powers of the original relaxation operator. -/
theorem compressedMeasure_moment (k : ℕ) (e g : Symmetric d) :
    ⟪e, action (tensorIntegral ν (fun r => r ^ k)) g⟫_ℝ =
      V.form ((relaxation V E X ^ k) (mismatch V E X (ι e)))
        (mismatch V E X (ι g)) := by
  rw [(compressedMeasure_integral V E X ι ν hν hαV hβV hαE hβE hV hE
    (fun r => r ^ k) (by fun_prop)).2 e g,
    cfc_pow_id _ _ (weightedRelaxation_isSelfAdjoint V E X)]
  let W := (WeightedSpace.continuousLinearEquiv (V.restrict X)).symm.conjContinuousAlgEquiv
  have hpow : weightedRelaxation V E X ^ k = W (relaxation V E X ^ k) :=
    (map_pow W (relaxation V E X) k).symm
  rw [hpow]
  rfl

/-- Appendix A.2 (`eq:K_laplace`): the spectral function `r exp(-r t)`
recovers the compressed semigroup kernel. -/
theorem compressedMeasure_memory (t : ℝ) (_ht : 0 ≤ t) (e g : Symmetric d) :
    ⟪e, action (tensorIntegral ν (fun r => r * Real.exp (-r * t))) g⟫_ℝ =
      memoryForm V E X ι t e g := by
  rw [(compressedMeasure_integral V E X ι ν hν hαV hβV hαE hβE hV hE
    (fun r => r * Real.exp (-r * t)) (by fun_prop)).2 e g]
  have hR := weightedRelaxation_isSelfAdjoint V E X
  have hf : (fun r : ℝ => Real.exp (-r * t)) =
      (fun r : ℝ => Real.exp (-t * r)) := by
    funext r
    congr 1
    ring
  rw [cfc_mul _ _ _ (by fun_prop) (by fun_prop), cfc_id' ℝ _ hR, hf,
    cfc_comp_const_mul _ Real.exp _ Real.continuous_exp.continuousOn hR,
    CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all _).smul hR),
    ← relaxationSemigroup_conjugate V E X t]
  let W := (WeightedSpace.continuousLinearEquiv (V.restrict X)).symm.conjContinuousAlgEquiv
  change ⟪(W (relaxation V E X) * W (relaxationSemigroup V E X t))
      (weightedMismatch V E X ι e), weightedMismatch V E X ι g⟫_ℝ = _
  rw [← map_mul]
  rfl

end KVApproximation.Spectral
