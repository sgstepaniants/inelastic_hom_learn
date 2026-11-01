module

public import KVApproximation.Homogenization.RescaledFieldProperties
public import KVApproximation.Homogenization.SpatialFormIdentities

/-!
# Coefficient combinations under periodic rescaling
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, combined elliptic coefficient: periodic rescaling
commutes with coefficient combinations as an equality of L∞ classes. -/
theorem rescaledCoefficient_add_smul {d : ℕ} (Ω : Opens (PhysicalSpace d))
    (A B : CoefficientField d ⊤) (c ε : ℝ) (hε : ε ≠ 0) :
    rescaledCoefficient Ω (A + c • B) ε hε =
      rescaledCoefficient Ω A ε hε + c • rescaledCoefficient Ω B ε hε := by
  have hcell : ∀ᵐ y ∂cellMeasure d,
      (A + c • B : CoefficientField d ⊤) y = A y + c • B y := by
    filter_upwards [Lp.coeFn_add A (c • B), Lp.coeFn_smul c B] with y ha hs
    rw [ha, Pi.add_apply, hs, Pi.smul_apply]
  have hphysical : ∀ᵐ x : PhysicalSpace d ∂volume,
      rescalePeriodic (A + c • B) ε x =
        rescalePeriodic A ε x + c • rescalePeriodic B ε x :=
    (quasiMeasurePreserving_scaledToCell hε).ae hcell
  apply Lp.ext
  filter_upwards [rescaledCoefficient_apply_ae Ω (A + c • B) ε hε,
    rescaledCoefficient_apply_ae Ω A ε hε, rescaledCoefficient_apply_ae Ω B ε hε,
    Lp.coeFn_add (rescaledCoefficient Ω A ε hε) (c • rescaledCoefficient Ω B ε hε),
    Lp.coeFn_smul c (rescaledCoefficient Ω B ε hε), ae_restrict_of_ae hphysical]
    with x hleft hA hB hadd hsmul hx
  rw [hleft, hadd, Pi.add_apply, hsmul, Pi.smul_apply, hA, hB]
  exact hx

/-- Theorem 3.1, transformed weak equation: linearity of the spatial
coefficient action passes through the actual L² strain map. -/
private theorem spatialForm_add_smul {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A B : Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d))))
    (c : ℝ) (u v : ZeroBoundaryH1 Ω) :
    spatialForm (A + c • B) u v =
      spatialForm A u v + c * spatialForm B u v := by
  have hp : (fun x => ⟪symmetricGradient u x, action ((A + c • B) x)
      (symmetricGradient v x)⟫_ℝ) =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
      fun x => ⟪symmetricGradient u x, action (A x) (symmetricGradient v x)⟫_ℝ +
        c * ⟪symmetricGradient u x, action (B x) (symmetricGradient v x)⟫_ℝ := by
    filter_upwards [Lp.coeFn_add A (c • B), Lp.coeFn_smul c B] with x ha hs
    rw [ha, Pi.add_apply, hs, Pi.smul_apply]
    change ⟪symmetricGradient u x, actionL d (A x + c • B x)
      (symmetricGradient v x)⟫_ℝ = _
    simp only [map_add, map_smul, add_apply, smul_apply, actionL_apply, inner_add_right]
    exact congrArg (fun r : ℝ =>
      ⟪symmetricGradient u x, action (A x) (symmetricGradient v x)⟫_ℝ + r)
      (real_inner_smul_right (symmetricGradient u x)
        (action (B x) (symmetricGradient v x)) c)
  unfold spatialForm
  rw [integral_congr_ae hp,
    integral_add (integrable_spatialForm A u v) ((integrable_spatialForm B u v).const_mul c),
    integral_const_mul]

/-- Theorem 3.1, transformed weak equation: the actual rescaled spatial
form splits into its viscous and elastic terms on any open domain. -/
theorem spatialForm_rescalePeriodic_add_smul {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A B : CoefficientField d ⊤) (c ε : ℝ) (hε : ε ≠ 0)
    (u v : ZeroBoundaryH1 Ω) :
    spatialForm (rescalePeriodic (A + c • B) ε) u v =
      spatialForm (rescalePeriodic A ε) u v +
        c * spatialForm (rescalePeriodic B ε) u v := by
  rw [← spatialForm_rescaledCoefficient Ω (A + c • B) ε hε u v,
    ← spatialForm_rescaledCoefficient Ω A ε hε u v,
    ← spatialForm_rescaledCoefficient Ω B ε hε u v,
    rescaledCoefficient_add_smul]
  exact spatialForm_add_smul (rescaledCoefficient Ω A ε hε)
    (rescaledCoefficient Ω B ε hε) c u v

end KVApproximation.Homogenization
