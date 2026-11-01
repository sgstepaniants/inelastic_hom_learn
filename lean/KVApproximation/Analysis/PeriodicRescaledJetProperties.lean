module

public import KVApproximation.Analysis.PeriodicRescaledJets
public import KVApproximation.Analysis.PeriodicSmoothIdentities

/-!
# Representatives and derivatives of rescaled jets
-/

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped ENNReal Gradient

namespace KVApproximation.Analysis.PeriodicRescaledJets

/-- Theorem 3.1: scalar jet coordinates retain the physical row ordering. -/
theorem jetCoordinate_apply {d : ℕ} (ε : ℝ) (i : Fin d)
    (z : PeriodicJet d) :
    jetCoordinate ε i z = WithLp.toLp 2
      (ε * WithLp.fst z i, WithLp.toLp 2 (fun j => WithLp.snd z (i, j))) := rfl

/-- Theorem 3.1: the pullback agrees almost everywhere with actual rescaling. -/
theorem rescaleJet_ae {d : ℕ} {Ω : Opens (PhysicalSpace d)} {ε : ℝ}
    (hq : Measurable (fun x : PhysicalSpace d => toCell (ε⁻¹ • x)))
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hbound : (volume.restrict (Ω : Set (PhysicalSpace d))).map
      (fun x => toCell (ε⁻¹ • x)) ≤ c • cellMeasure d) (w : PeriodicJetField d) :
    rescaleJet hq hc hbound w =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
      rescalePeriodic w ε := by
  exact (Lp.coeFn_compMeasurePreserving
    (Lp.LpToLpOfMeasureLeSMul hc hbound w)
    (hq.measurePreserving (volume.restrict (Ω : Set (PhysicalSpace d))))).trans
      ((hq.measurePreserving (volume.restrict (Ω : Set (PhysicalSpace d)))).quasiMeasurePreserving.ae
        (Lp.coeFn_LpToLpOfMeasureLeSMul hc hbound w))

/-- Theorem 3.1: the smooth chain rule cancels the displacement amplitude
against the inverse spatial scale. -/
theorem gradient_scaled_component {d : ℕ}
    (φ : PeriodicC1 d (PhysicalSpace d)) {ε : ℝ} (hε : ε ≠ 0)
    (i : Fin d) (x : PhysicalSpace d) :
    (∇ (fun z : PhysicalSpace d => ε * φ.value (toCell (ε⁻¹ • z)) i)) x =
      WithLp.toLp 2 (fun j => periodicGradient φ.value (toCell (ε⁻¹ • x)) (i, j)) := by
  let P := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i
  let L : PhysicalSpace d →L[ℝ] PhysicalSpace d := ε⁻¹ • ContinuousLinearMap.id ℝ _
  have hd := ((P.hasFDerivAt.comp (ε⁻¹ • x)
    ((φ.contDiff_lift.differentiable one_ne_zero) (ε⁻¹ • x)).hasFDerivAt).comp x
      L.hasFDerivAt).const_mul ε
  change HasFDerivAt (fun z : PhysicalSpace d => ε * φ.value (toCell (ε⁻¹ • z)) i)
    _ x at hd
  apply PiLp.ext
  intro j
  have hg := inner_gradient_left (𝕜 := ℝ)
    (f := fun z : PhysicalSpace d => ε * φ.value (toCell (ε⁻¹ • z)) i)
    (x := x) (y := EuclideanSpace.single j 1)
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at hg
  rw [hg, hd.fderiv]
  change ε * (fderiv ℝ (fun z : PhysicalSpace d => φ.value (toCell z))
    (ε⁻¹ • x) (ε⁻¹ • EuclideanSpace.single j 1)) i = _
  rw [map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  exact (congrArg (fun z : PhysicalSpace d => z i) (φ.partial_toCell j (ε⁻¹ • x))).symm

end KVApproximation.Analysis.PeriodicRescaledJets
