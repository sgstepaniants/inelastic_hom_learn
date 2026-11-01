module

public import KVApproximation.NeuralOperators.FeedforwardFourierMapping
public import KVApproximation.NeuralOperators.FeedforwardProperties
public import KVApproximation.NeuralOperators.NonlinearChannelLifting
public import KVApproximation.NeuralOperators.FourierMappingLayers
public import KVApproximation.NeuralOperators.FourierMappingProjection

/-!
# Regularity with feedforward lifting and output
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1: Fourier projection depends only on the field's a.e. class. -/
private theorem projection_congr {d input output : ℕ}
    (P : FourierProjection d input output) {h g : PeriodicCell d → Channels input}
    (hfg : h =ᵐ[cellMeasure d] g) : P.eval h = P.eval g := by
  have hc (k : Fin d → ℤ) (j : Fin input) : channelFourier h k j = channelFourier g k j := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  simp only [FourierProjection.eval, FourierProjection.complexValue, hc]

/-- Example 2.1: the feedforward architecture respects null-set changes
in the field representative. No activation regularity is needed for equality. -/
theorem FeedforwardFourierMapping.evalRepresentative_congr
    {d vectorInput functionInput output : ℕ}
    (P : FeedforwardFourierMapping d vectorInput functionInput output)
    (σLift σFourier σOutput : ℝ → ℝ) (v : Channels vectorInput)
    {h g : PeriodicCell d → Channels functionInput} (hfg : h =ᵐ[cellMeasure d] g) :
    P.evalRepresentative σLift σFourier σOutput v h =
      P.evalRepresentative σLift σFourier σOutput v g := by
  apply congrArg (P.outputMap.eval σOutput)
  apply projection_congr
  apply P.layers.eval_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- Example 2.1 and Remark 4.3: global Lipschitz activations in the lifting
and Fourier layers give an actual globally Lipschitz L² hidden-field map.
This is the growth-qualified form of the nonlinear lifting assertion. -/
theorem FeedforwardFourierMapping.exists_lipschitz_hidden
    {d vectorInput functionInput output : ℕ}
    (P : FeedforwardFourierMapping d vectorInput functionInput output)
    {σLift σFourier : ℝ → ℝ} {KL KF : NNReal}
    (hLift : LipschitzWith KL σLift) (hFourier : LipschitzWith KF σFourier) :
    ∃ K : NNReal,
      ∃ F : Channels vectorInput × ChannelField d functionInput → ChannelField d P.hiddenWidth,
        LipschitzWith K F ∧ ∀ x : Channels vectorInput × ChannelField d functionInput,
          (F x : PeriodicCell d → Channels P.hiddenWidth) =ᵐ[cellMeasure d]
            P.hiddenRepresentative σLift σFourier x.1 x.2 := by
  obtain ⟨KS, hS⟩ := P.lifting.lipschitz hLift
  obtain ⟨KA, A, hA, hArep⟩ := exists_lipschitz_channel_lifting (d := d) hS
  obtain ⟨KF', F, hF, hFrep⟩ := P.layers.exists_lipschitz_evalLp hFourier
  refine ⟨KF' * KA, F ∘ A, hF.comp hA, ?_⟩
  intro x
  exact (hFrep (A x)).trans (P.layers.eval_congr_ae σFourier (hArep x))

/-- Remarks 4.2–4.3: after growth-qualified lifting and Lipschitz Fourier
layers, locally Lipschitz output activations give a locally Lipschitz map
on the full vector–L² product, hence in the vector input at each material. -/
theorem FeedforwardFourierMapping.locallyLipschitz
    {d vectorInput functionInput output : ℕ}
    (P : FeedforwardFourierMapping d vectorInput functionInput output)
    {σLift σFourier σOutput : ℝ → ℝ} {KL KF : NNReal}
    (hLift : LipschitzWith KL σLift) (hFourier : LipschitzWith KF σFourier)
    (hOutput : LocallyLipschitz σOutput) :
    LocallyLipschitz (P.eval σLift σFourier σOutput) := by
  obtain ⟨K, F, hF, hFrep⟩ := P.exists_lipschitz_hidden hLift hFourier
  obtain ⟨B, hB⟩ := P.projection.exists_evalCLM
  have heq : P.eval σLift σFourier σOutput = fun x => P.outputMap.eval σOutput (B (F x)) := by
    funext x
    rw [hB]
    apply congrArg (P.outputMap.eval σOutput)
    exact projection_congr P.projection (hFrep x).symm
  rw [heq]
  exact (P.outputMap.locallyLipschitz hOutput).comp
    (B.lipschitzWith.locallyLipschitz.comp hF.locallyLipschitz)

end KVApproximation.NeuralOperators
