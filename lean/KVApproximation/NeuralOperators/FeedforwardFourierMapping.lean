module

public import KVApproximation.NeuralOperators.Feedforward
public import KVApproximation.NeuralOperators.FourierMapping

/-!
# Fourier mappings with feedforward lifting and output
-/

@[expose] public section

noncomputable section

open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remark 4.3: the same finite Fourier architecture with
finite feedforward networks for the pointwise lifting and vector output. -/
structure FeedforwardFourierMapping (d vectorInput functionInput output : ℕ) where
  liftWidth : ℕ
  hiddenWidth : ℕ
  projectionWidth : ℕ
  lifting : Feedforward (WithLp 2 (Channels vectorInput × Channels functionInput)) liftWidth
  layers : FourierChain d liftWidth hiddenWidth
  projection : FourierProjection d hiddenWidth projectionWidth
  outputMap : Feedforward (Channels projectionWidth) output

/-- Example 2.1: the hidden field after nonlinear lifting and Fourier layers. -/
def FeedforwardFourierMapping.hiddenRepresentative {d vectorInput functionInput output : ℕ}
    (P : FeedforwardFourierMapping d vectorInput functionInput output)
    (σLift σFourier : ℝ → ℝ) (v : Channels vectorInput)
    (h : PeriodicCell d → Channels functionInput) : PeriodicCell d → Channels P.hiddenWidth :=
  P.layers.eval σFourier (fun y => P.lifting.eval σLift (WithLp.toLp 2 (v, h y)))

/-- Example 2.1: representative evaluation followed by finite Fourier
projection and the feedforward output network. -/
def FeedforwardFourierMapping.evalRepresentative {d vectorInput functionInput output : ℕ}
    (P : FeedforwardFourierMapping d vectorInput functionInput output)
    (σLift σFourier σOutput : ℝ → ℝ) (v : Channels vectorInput)
    (h : PeriodicCell d → Channels functionInput) : Channels output :=
  P.outputMap.eval σOutput (P.projection.eval (P.hiddenRepresentative σLift σFourier v h))

/-- Example 2.1: evaluation on the vector and actual L² material input. -/
def FeedforwardFourierMapping.eval {d vectorInput functionInput output : ℕ}
    (P : FeedforwardFourierMapping d vectorInput functionInput output)
    (σLift σFourier σOutput : ℝ → ℝ)
    (x : Channels vectorInput × ChannelField d functionInput) : Channels output :=
  P.evalRepresentative σLift σFourier σOutput x.1 x.2

/-- Remark 4.3: the class of continuous maps represented by finite
feedforward lifting and output networks and the prescribed Fourier layers. -/
def feedforwardFourierMappingClass (σLift σFourier σOutput : ℝ → ℝ)
    (d vectorInput functionInput output : ℕ) :
    Set C(Channels vectorInput × ChannelField d functionInput, Channels output) :=
  {Φ | ∃ P : FeedforwardFourierMapping d vectorInput functionInput output,
    ∀ x, Φ x = P.eval σLift σFourier σOutput x}

/-- Remark 4.3: linear lifting and output are the zero-bias affine-only
feedforward networks, with the original finite Fourier data unchanged. -/
def FourierMapping.toFeedforward {d vectorInput functionInput output : ℕ}
    (P : FourierMapping d vectorInput functionInput output) :
    FeedforwardFourierMapping d vectorInput functionInput output where
  liftWidth := P.liftWidth
  hiddenWidth := P.hiddenWidth
  projectionWidth := P.projectionWidth
  lifting := .affine P.lifting 0
  layers := P.layers
  projection := P.projection
  outputMap := .affine P.outputMap 0

end KVApproximation.NeuralOperators
