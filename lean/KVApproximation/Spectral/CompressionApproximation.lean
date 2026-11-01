module

public import KVApproximation.Spectral.CompressionIntegration

/-!
# Uniform approximation in the compressed functional calculus
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.OperatorTheory KVApproximation.Tensor

namespace KVApproximation.Spectral

/-- Lemma B.5 (`eq:weak_converge_decomposed`): each continuous-test
remainder has the paper's dimension-independent mismatch-energy bound. -/
theorem compressedMeasure_pairing_sub_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {d : ℕ} (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
    (hν : IsCompressedMeasure V E X ι ν)
    {αV βV αE βE : ℝ} (hαV : 0 < αV) (hβV : 0 < βV)
    (hαE : 0 < αE) (hβE : 0 < βE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (αE / βV) (βE / αV)))
    (hg : ContinuousOn g (Set.Icc (αE / βV) (βE / αV)))
    {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ r ∈ Set.Icc (αE / βV) (βE / αV), |f r - g r| ≤ ε)
    (e k : Symmetric d) :
    |⟪e, action (tensorIntegral ν f) k⟫_ℝ -
      ⟪e, action (tensorIntegral ν g) k⟫_ℝ| ≤
      ε * (βV * βE / αE) * ‖ι e‖ * ‖ι k‖ := by
  let R := weightedRelaxation V E X
  let D := weightedMismatch V E X ι
  let B := βV * βE / αE
  have hB : 0 ≤ B := (div_pos (mul_pos hβV hβE) hαE).le
  have hmismatch (u : Symmetric d) : ‖D u‖ ≤ Real.sqrt B * ‖ι u‖ := by
    have hsq : ‖D u‖ ^ 2 ≤ B * ‖ι u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (D u)]
      exact mismatch_energy_le V E X hαE hβV.le hV hE (ι u)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg B) (norm_nonneg _))).1
    rwa [mul_pow, Real.sq_sqrt hB]
  have hspec : spectrum ℝ R ⊆ Set.Icc (αE / βV) (βE / αV) := by
    rw [weightedRelaxation_spectrum_eq]
    exact relaxation_spectrum_subset V E X hαV hβV hαE hβE hV hE
  have hcfc : ‖cfc (fun r => f r - g r) R‖ ≤ ε := by
    rw [← ContinuousLinearMap.norm_complexifyL2,
      ContinuousLinearMap.complexifyL2_cfc (fun r => f r - g r) R ((hf.sub hg).mono hspec)
        (weightedRelaxation_isSelfAdjoint V E X)]
    apply norm_cfc_le hε
    intro r hr
    have hr' : r ∈ spectrum ℝ R := by
      rwa [ContinuousLinearMap.spectrum_complexifyL2
        (weightedRelaxation_isSelfAdjoint V E X)] at hr
    exact happrox r (hspec hr')
  rw [(compressedMeasure_integral V E X ι ν hν hαV hβV hαE hβE hV hE f hf).2 e k,
    (compressedMeasure_integral V E X ι ν hν hαV hβV hαE hβE hV hE g hg).2 e k]
  change |⟪cfc f R (D e), D k⟫_ℝ - ⟪cfc g R (D e), D k⟫_ℝ| ≤ _
  rw [← inner_sub_left, ← sub_apply, ← cfc_sub f g R (hf.mono hspec) (hg.mono hspec)]
  calc
    _ ≤ ‖cfc (fun r => f r - g r) R (D e)‖ * ‖D k‖ := abs_real_inner_le_norm _ _
    _ ≤ (ε * ‖D e‖) * ‖D k‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact ((cfc (fun r => f r - g r) R).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hcfc (norm_nonneg _))
    _ ≤ (ε * (Real.sqrt B * ‖ι e‖)) * (Real.sqrt B * ‖ι k‖) := by
      gcongr
      · exact hmismatch e
      · exact hmismatch k
    _ = _ := by
      have hsqrt := Real.sq_sqrt hB
      change ε * (Real.sqrt B * ‖ι e‖) * (Real.sqrt B * ‖ι k‖) = ε * B * ‖ι e‖ * ‖ι k‖
      calc
        _ = ε * (Real.sqrt B ^ 2) * ‖ι e‖ * ‖ι k‖ := by ring
        _ = _ := by rw [hsqrt]

end KVApproximation.Spectral
