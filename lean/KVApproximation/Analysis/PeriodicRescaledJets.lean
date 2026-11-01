module

public import KVApproximation.Analysis.PeriodicSobolev
public import KVApproximation.Analysis.PeriodicRescaling
public import KVApproximation.Analysis.VectorSobolevFields

/-!
# Coordinate jets of periodic rescalings

A dominated-measure pullback transports periodic L² jets. Coordinate
projection records the displacement amplitude and the full gradient row.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped ENNReal

namespace KVApproximation.Analysis.PeriodicRescaledJets

/-- Theorem 3.1, oscillating corrector tests: extract one scalar jet,
scaling the displacement value while retaining its full gradient row. -/
def jetCoordinate {d : ℕ} (ε : ℝ) (i : Fin d) :
    PeriodicJet d →L[ℝ] TauCeti.Sobolev1Jet (PhysicalSpace d) :=
  let V := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i).comp
    (WithLp.fstL 2 ℝ (PhysicalSpace d) (SecondOrder d))
  let G := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => PhysicalSpace d) i).comp
    ((gradientRowCoordinates d).symm.toContinuousLinearMap.comp
      (WithLp.sndL 2 ℝ (PhysicalSpace d) (SecondOrder d)))
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (PhysicalSpace d)).symm.toContinuousLinearMap.comp
    ((ε • V).prod G)

/-- Theorem 3.1, oscillating corrector tests: actual L² pullback of
periodic jets under a finite pushforward-measure bound. -/
def rescaleJet {d : ℕ} {Ω : Opens (PhysicalSpace d)} {ε : ℝ}
    (hq : Measurable (fun x : PhysicalSpace d => toCell (ε⁻¹ • x)))
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hbound : (volume.restrict (Ω : Set (PhysicalSpace d))).map
      (fun x => toCell (ε⁻¹ • x)) ≤ c • cellMeasure d) :
    PeriodicJetField d →L[ℝ]
      Lp (PeriodicJet d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
  (Lp.compMeasurePreservingₗᵢ ℝ _
    (hq.measurePreserving (volume.restrict (Ω : Set (PhysicalSpace d))))).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul hc hbound)

end KVApproximation.Analysis.PeriodicRescaledJets
