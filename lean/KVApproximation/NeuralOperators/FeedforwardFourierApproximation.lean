module

public import KVApproximation.NeuralOperators.FeedforwardFourierMapping
public import KVApproximation.NeuralOperators.FourierMappingApproximation

/-!
# Approximation with feedforward lifting and output

Affine-only lifting and output reproduce the linear architecture exactly,
so the same approximators belong to the larger feedforward class.
-/

public section

namespace KVApproximation.NeuralOperators

/-- Remark 4.3: the feedforward class contains the original linear
lifting/output class exactly, through affine-only networks. -/
theorem fourierMappingClass_subset_feedforward (σLift σFourier σOutput : ℝ → ℝ)
    (d vectorInput functionInput output : ℕ) :
    fourierMappingClass σFourier d vectorInput functionInput output ⊆
      feedforwardFourierMappingClass σLift σFourier σOutput d vectorInput functionInput output := by
  rintro Φ ⟨P, hP⟩
  refine ⟨P.toFeedforward, fun x => ?_⟩
  rw [hP x]
  simp only [FourierMapping.eval, FourierMapping.evalRepresentative,
    FeedforwardFourierMapping.eval, FeedforwardFourierMapping.evalRepresentative,
    FeedforwardFourierMapping.hiddenRepresentative, FourierMapping.toFeedforward,
    Feedforward.eval, add_zero]
  rfl

/-- Remark 4.3: the feedforward architecture satisfies A1 through its
linear-lifting/output subfamily, for the same Fourier activation hypotheses. -/
theorem feedforwardFourierMappingClass_universal (σLift σOutput : ℝ → ℝ)
    {σFourier : ℝ → ℝ} (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σFourier)
    {K : NNReal} (hLip : LipschitzWith K σFourier)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σFourier x = p.eval x)
    (d vectorInput functionInput output : ℕ) :
    HasUniversalApproximation
      (feedforwardFourierMappingClass σLift σFourier σOutput d vectorInput functionInput output) := by
  intro V M hV hM g ε hε
  obtain ⟨Φ, hΦ, herror⟩ :=
    fourierMappingClass_universal hSmooth hLip hNonpoly d vectorInput functionInput output
      V M hV hM g ε hε
  exact ⟨Φ, fourierMappingClass_subset_feedforward σLift σFourier σOutput
    d vectorInput functionInput output hΦ, herror⟩

/-- Remark 4.3: the same approximator from the linear subfamily supplies
A2 for the architecture with feedforward lifting and output. -/
theorem feedforwardFourierMappingClass_locallyLipschitz_universal (σLift σOutput : ℝ → ℝ)
    {σFourier : ℝ → ℝ} (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σFourier)
    {K : NNReal} (hLip : LipschitzWith K σFourier)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σFourier x = p.eval x)
    (d vectorInput functionInput output : ℕ) :
    HasLocallyLipschitzApproximation
      (feedforwardFourierMappingClass σLift σFourier σOutput d vectorInput functionInput output) := by
  intro V M hV hM g ε hε
  obtain ⟨Φ, hΦ, herror, hlocal⟩ :=
    fourierMappingClass_locallyLipschitz_universal hSmooth hLip hNonpoly
      d vectorInput functionInput output V M hV hM g ε hε
  exact ⟨Φ, fourierMappingClass_subset_feedforward σLift σFourier σOutput
    d vectorInput functionInput output hΦ, herror, hlocal⟩

end KVApproximation.NeuralOperators
