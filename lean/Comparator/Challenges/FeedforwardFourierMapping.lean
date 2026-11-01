module

public import KVApproximation.NeuralOperators.FeedforwardFourierMapping
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Admissibility with feedforward lifting and output
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1: the feedforward architecture respects null-set changes
in the field representative. No activation regularity is needed for equality. -/
theorem FeedforwardFourierMapping.evalRepresentative_congr
    {d vectorInput functionInput output : ℕ}
    (P : FeedforwardFourierMapping d vectorInput functionInput output)
    (σLift σFourier σOutput : ℝ → ℝ) (v : Channels vectorInput)
    {h g : PeriodicCell d → Channels functionInput} (hfg : h =ᵐ[cellMeasure d] g) :
    P.evalRepresentative σLift σFourier σOutput v h =
      P.evalRepresentative σLift σFourier σOutput v g := by
  sorry

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
  sorry

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
  sorry

/-- Remark 4.3: the feedforward class contains the original linear
lifting/output class exactly, through affine-only networks. -/
theorem fourierMappingClass_subset_feedforward (σLift σFourier σOutput : ℝ → ℝ)
    (d vectorInput functionInput output : ℕ) :
    fourierMappingClass σFourier d vectorInput functionInput output ⊆
      feedforwardFourierMappingClass σLift σFourier σOutput d vectorInput functionInput output := by
  sorry

/-- Remark 4.3: the feedforward architecture satisfies A1 through its
linear-lifting/output subfamily, for the same Fourier activation hypotheses. -/
theorem feedforwardFourierMappingClass_universal (σLift σOutput : ℝ → ℝ)
    {σFourier : ℝ → ℝ} (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σFourier)
    {K : NNReal} (hLip : LipschitzWith K σFourier)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σFourier x = p.eval x)
    (d vectorInput functionInput output : ℕ) :
    HasUniversalApproximation
      (feedforwardFourierMappingClass σLift σFourier σOutput d vectorInput functionInput output) := by
  sorry

/-- Remark 4.3: the same approximator from the linear subfamily supplies
A2 for the architecture with feedforward lifting and output. -/
theorem feedforwardFourierMappingClass_locallyLipschitz_universal (σLift σOutput : ℝ → ℝ)
    {σFourier : ℝ → ℝ} (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σFourier)
    {K : NNReal} (hLip : LipschitzWith K σFourier)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σFourier x = p.eval x)
    (d vectorInput functionInput output : ℕ) :
    HasLocallyLipschitzApproximation
      (feedforwardFourierMappingClass σLift σFourier σOutput d vectorInput functionInput output) := by
  sorry

end KVApproximation.NeuralOperators
