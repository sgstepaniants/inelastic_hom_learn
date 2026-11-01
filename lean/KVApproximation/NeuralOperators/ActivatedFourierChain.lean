module

public import KVApproximation.NeuralOperators.FourierMapping

/-!
# Fourier chains with layer-dependent activations
-/

@[expose] public section

noncomputable section

open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1: a finite Fourier chain with an independently chosen
activation at each layer and arbitrary intermediate channel widths. -/
inductive ActivatedFourierChain (d : ℕ) : ℕ → ℕ → Type where
  | nil (width : ℕ) : ActivatedFourierChain d width width
  | cons {input middle output : ℕ} (layer : FourierLayer d input middle)
      (activation : ℝ → ℝ) (rest : ActivatedFourierChain d middle output) :
      ActivatedFourierChain d input output

/-- Example 2.1: composition with the prescribed layer-dependent activations. -/
def ActivatedFourierChain.eval {d input output : ℕ} :
    ActivatedFourierChain d input output → (PeriodicCell d → Channels input) →
      PeriodicCell d → Channels output
  | .nil _, h => h
  | .cons L σ rest, h => rest.eval (L.eval σ h)

/-- Example 2.1 and Remark 4.3: every layer activation has a global
Lipschitz bound; the constants may differ between layers. -/
def ActivatedFourierChain.HasLipschitzActivations {d input output : ℕ} :
    ActivatedFourierChain d input output → Prop
  | .nil _ => True
  | .cons _ σ rest => (∃ K : NNReal, LipschitzWith K σ) ∧ rest.HasLipschitzActivations

/-- Example 2.1 and Remark 4.3: the shared-activation family used in
the approximation proof is an actual layer-dependent chain. -/
def FourierChain.withActivation {d input output : ℕ} (σ : ℝ → ℝ) :
    FourierChain d input output → ActivatedFourierChain d input output
  | .nil width => .nil width
  | .cons L rest => .cons L σ (rest.withActivation σ)

end KVApproximation.NeuralOperators
