module

public import KVApproximation.NeuralOperators.FourierMappingLayers
public import KVApproximation.NeuralOperators.FourierMappingProjection
public import KVApproximation.NeuralOperators.ChannelLifting

/-!
# Global Lipschitz continuity of Fourier neural mappings
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1, projection ingredient: null-set changes in the hidden
field leave every Fourier coefficient and the projected output unchanged. -/
private theorem projection_eval_congr_ae {d input output : ℕ}
    (P : FourierProjection d input output) {h g : PeriodicCell d → Channels input}
    (hfg : h =ᵐ[cellMeasure d] g) : P.eval h = P.eval g := by
  have hc (k : Fin d → ℤ) (j : Fin input) : channelFourier h k j = channelFourier g k j := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  simp only [FourierProjection.eval, FourierProjection.complexValue, hc]

/-- Remark 4.3: globally Lipschitz activations make every finite mapping
globally Lipschitz on the full L² input space, hence continuous and locally
Lipschitz in its vector input. -/
theorem FourierMapping.lipschitz {d vectorInput functionInput output : ℕ}
    (P : FourierMapping d vectorInput functionInput output) {σ : ℝ → ℝ}
    {K : NNReal} (hσ : LipschitzWith K σ) :
    ∃ L : NNReal, LipschitzWith L (P.eval σ) := by
  obtain ⟨A, hA⟩ := exists_channel_liftingCLM (d := d) P.lifting
  obtain ⟨K', F, hF, hFrep⟩ := P.layers.exists_lipschitz_evalLp hσ
  obtain ⟨B, hB⟩ := P.projection.exists_evalCLM
  let R : ChannelField d P.hiddenWidth →L[ℝ] Channels output :=
    P.outputMap.toContinuousLinearMap.comp B
  have heval (x : Channels vectorInput × ChannelField d functionInput) :
      R (F (A x)) = P.eval σ x := by
    change P.outputMap (B (F (A x))) = P.outputMap
      (P.projection.eval (P.layers.eval σ
        (fun y => P.lifting (WithLp.toLp 2 (x.1, x.2 y)))))
    rw [hB]
    apply congrArg P.outputMap
    exact projection_eval_congr_ae P.projection
      ((hFrep (A x)).trans (P.layers.eval_congr_ae σ (hA x)))
  have heq : P.eval σ = fun x => R (F (A x)) := funext (fun x => (heval x).symm)
  refine ⟨‖R‖₊ * K' * ‖A‖₊, ?_⟩
  rw [heq]
  exact (R.lipschitzWith.comp hF).comp A.lipschitzWith

end KVApproximation.NeuralOperators
