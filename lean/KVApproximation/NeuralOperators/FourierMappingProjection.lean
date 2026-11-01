module

public import KVApproximation.NeuralOperators.FourierMapping
public import KVApproximation.Analysis.PeriodicFourierFunctionals

/-!
# Continuous linear Fourier projection
-/

public section

noncomputable section

open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remark 4.3: the finite Fourier projection defines an
actual continuous real-linear map on Euclidean L² channel fields. -/
theorem FourierProjection.exists_evalCLM {d input output : ℕ}
    (P : FourierProjection d input output) :
    ∃ A : ChannelField d input →L[ℝ] Channels output,
      ∀ h : ChannelField d input, A h = P.eval h := by
  classical
  let c (k : Fin d → ℤ) (j : Fin input) : ChannelField d input →L[ℝ] ℂ :=
    (exists_periodicFourierCoefficientCLM k j).choose
  have hc (k : Fin d → ℤ) (j : Fin input) (h : ChannelField d input) :
      c k j h = channelFourier h k j :=
    (exists_periodicFourierCoefficientCLM k j).choose_spec h
  let B (i : Fin output) : ChannelField d input →L[ℝ] ℂ :=
    ∑ k ∈ frequencyBox P.cutoff, ∑ j : Fin input, P.multiplier k i j • c k j
  let A : ChannelField d input →L[ℝ] Channels output :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin output => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => Complex.reCLM.comp (B i))
  refine ⟨A, ?_⟩
  intro h
  apply PiLp.ext
  intro i
  change (B i h).re = (P.complexValue h i).re
  apply congrArg Complex.re
  simp only [B, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hc, FourierProjection.complexValue]

end KVApproximation.NeuralOperators
