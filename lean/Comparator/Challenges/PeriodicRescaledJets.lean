module

public import KVApproximation.Analysis.PeriodicRescaledJets
public import KVApproximation.Analysis.PeriodicSmoothIdentities

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped ENNReal Gradient

namespace KVApproximation.Analysis.PeriodicRescaledJets

/-- Theorem 3.1: scalar jet coordinates retain the physical row ordering. -/
theorem jetCoordinate_apply {d : ℕ} (ε : ℝ) (i : Fin d)
    (z : PeriodicJet d) :
    jetCoordinate ε i z = WithLp.toLp 2
      (ε * WithLp.fst z i, WithLp.toLp 2 (fun j => WithLp.snd z (i, j))) := by
  sorry

/-- Theorem 3.1: the pullback agrees almost everywhere with actual rescaling. -/
theorem rescaleJet_ae {d : ℕ} {Ω : Opens (PhysicalSpace d)} {ε : ℝ}
    (hq : Measurable (fun x : PhysicalSpace d => toCell (ε⁻¹ • x)))
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hbound : (volume.restrict (Ω : Set (PhysicalSpace d))).map
      (fun x => toCell (ε⁻¹ • x)) ≤ c • cellMeasure d) (w : PeriodicJetField d) :
    rescaleJet hq hc hbound w =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
      rescalePeriodic w ε := by
  sorry

/-- Theorem 3.1: the smooth chain rule cancels the displacement amplitude
against the inverse spatial scale. -/
theorem gradient_scaled_component {d : ℕ}
    (φ : PeriodicC1 d (PhysicalSpace d)) {ε : ℝ} (hε : ε ≠ 0)
    (i : Fin d) (x : PhysicalSpace d) :
    (∇ (fun z : PhysicalSpace d => ε * φ.value (toCell (ε⁻¹ • z)) i)) x =
      WithLp.toLp 2 (fun j => periodicGradient φ.value (toCell (ε⁻¹ • x)) (i, j)) := by
  sorry

end KVApproximation.Analysis.PeriodicRescaledJets
