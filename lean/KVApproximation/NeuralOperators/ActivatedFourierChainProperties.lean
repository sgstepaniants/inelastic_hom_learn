module

public import KVApproximation.NeuralOperators.ActivatedFourierChain
public import KVApproximation.NeuralOperators.FourierMappingLayers
public import KVApproximation.NeuralOperators.FourierMappingLp

/-!
# Regularity of layer-dependent Fourier chains
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1: independently activated Fourier chains respect a.e.
equality of the input field, with no regularity assumption on activations. -/
theorem ActivatedFourierChain.eval_congr_ae {d input output : ℕ}
    (L : ActivatedFourierChain d input output)
    {h g : PeriodicCell d → Channels input} (hfg : h =ᵐ[cellMeasure d] g) :
    L.eval h =ᵐ[cellMeasure d] L.eval g := by
  induction L with
  | nil width => exact hfg
  | cons L σ rest ih => exact ih (L.eval_congr_ae σ hfg)

/-- Example 2.1: global Lipschitz bounds for the individual activations
ensure that the output field of the finite chain belongs to L². -/
theorem ActivatedFourierChain.memLp_eval {d input output : ℕ}
    (L : ActivatedFourierChain d input output) (hL : L.HasLipschitzActivations)
    {h : PeriodicCell d → Channels input} (hh : MemLp h 2 (cellMeasure d)) :
    MemLp (L.eval h) 2 (cellMeasure d) := by
  induction L with
  | nil width => exact hh
  | cons L σ rest ih =>
      obtain ⟨⟨K, hσ⟩, hrest⟩ := hL
      exact ih hrest (L.memLp_eval hσ hh)

/-- Example 2.1 and Remark 4.3: a finite chain with individually Lipschitz
activations has an actual globally Lipschitz L² realization. -/
theorem ActivatedFourierChain.exists_lipschitz_evalLp {d input output : ℕ}
    (L : ActivatedFourierChain d input output) (hL : L.HasLipschitzActivations) :
    ∃ K : NNReal, ∃ F : ChannelField d input → ChannelField d output,
      LipschitzWith K F ∧ ∀ h : ChannelField d input,
        (F h : PeriodicCell d → Channels output) =ᵐ[cellMeasure d] L.eval h := by
  induction L with
  | nil width => exact ⟨1, id, LipschitzWith.id, fun _ => Filter.EventuallyEq.rfl⟩
  | cons L σ rest ih =>
      obtain ⟨⟨K, hσ⟩, hrest⟩ := hL
      obtain ⟨K₁, F, hF, hFrep⟩ := L.exists_lipschitz_evalLp hσ
      obtain ⟨K₂, G, hG, hGrep⟩ := ih hrest
      refine ⟨K₂ * K₁, G ∘ F, hG.comp hF, ?_⟩
      intro h
      exact (hGrep (F h)).trans (rest.eval_congr_ae (hFrep h))

/-- Example 2.1 and Remark 4.3: specializing every layer to one activation
recovers exactly the evaluator used in the universal-approximation proof. -/
theorem FourierChain.withActivation_eval {d input output : ℕ}
    (L : FourierChain d input output) (σ : ℝ → ℝ)
    (h : PeriodicCell d → Channels input) :
    (L.withActivation σ).eval h = L.eval σ h := by
  induction L with
  | nil width => rfl
  | cons L rest ih => exact ih (L.eval σ h)

end KVApproximation.NeuralOperators
