module

public import KVApproximation.NeuralOperators.FourierMapping

/-!
# Representative independence of Fourier neural mappings
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1, Fourier coefficients: changing the input on a null set
leaves every coefficient unchanged. -/
private theorem channelFourier_congr_ae {d n : ℕ}
    {h g : PeriodicCell d → Channels n} (hfg : h =ᵐ[cellMeasure d] g)
    (k : Fin d → ℤ) (j : Fin n) : channelFourier h k j = channelFourier g k j := by
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- Example 2.1: layer evaluation respects equality almost everywhere. -/
theorem FourierLayer.eval_congr_ae {d input output : ℕ} (L : FourierLayer d input output)
    (σ : ℝ → ℝ) {h g : PeriodicCell d → Channels input}
    (hfg : h =ᵐ[cellMeasure d] g) : L.eval σ h =ᵐ[cellMeasure d] L.eval σ g := by
  filter_upwards [hfg] with y hy
  simp only [FourierLayer.eval, FourierLayer.fourierPart,
    channelFourier_congr_ae hfg, hy]

/-- Example 2.1: finite chains respect equality almost everywhere. -/
theorem FourierChain.eval_congr_ae {d input output : ℕ} (L : FourierChain d input output)
    (σ : ℝ → ℝ) {h g : PeriodicCell d → Channels input}
    (hfg : h =ᵐ[cellMeasure d] g) : L.eval σ h =ᵐ[cellMeasure d] L.eval σ g := by
  induction L with
  | nil width => exact hfg
  | cons L rest ih => exact ih (L.eval_congr_ae σ hfg)

/-- Example 2.1: the full mapping does not depend on the L² representative. -/
theorem FourierMapping.evalRepresentative_congr {d vectorInput functionInput output : ℕ}
    (P : FourierMapping d vectorInput functionInput output) (σ : ℝ → ℝ)
    (v : Channels vectorInput) {h g : PeriodicCell d → Channels functionInput}
    (hfg : h =ᵐ[cellMeasure d] g) :
    P.evalRepresentative σ v h = P.evalRepresentative σ v g := by
  have hlift : (fun y => P.lifting (WithLp.toLp 2 (v, h y))) =ᵐ[cellMeasure d]
      (fun y => P.lifting (WithLp.toLp 2 (v, g y))) := by
    filter_upwards [hfg] with y hy
    rw [hy]
  have hchain := P.layers.eval_congr_ae σ hlift
  simp only [FourierMapping.evalRepresentative, FourierProjection.eval,
    FourierProjection.complexValue, channelFourier_congr_ae hchain]

end KVApproximation.NeuralOperators
