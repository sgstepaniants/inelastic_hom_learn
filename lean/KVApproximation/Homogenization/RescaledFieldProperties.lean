module

public import KVApproximation.Homogenization.RescaledFields
public import KVApproximation.Tensor.FieldBounds

/-!
# Physical representatives and uniform periodic coefficient bounds
-/

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} (Ω : Opens (PhysicalSpace d))
  (A : CoefficientField d ⊤) (ε : ℝ) (hε : ε ≠ 0)

/-- Theorem 3.1, microscopic coefficients: the spatial L∞ class has
the actual periodically rescaled coefficient as an a.e. representative. -/
theorem rescaledCoefficient_apply_ae :
    rescaledCoefficient Ω A ε hε =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
      rescalePeriodic A ε := by
  exact MemLp.coeFn_toLp _

/-- Theorem 3.1, uniform coefficient estimates: restriction and periodic
rescaling retain the original L∞ Frobenius norm bound. -/
theorem norm_rescaledCoefficient_le :
    ‖rescaledCoefficient Ω A ε hε‖ ≤ ‖A‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top A)
  rw [eLpNorm_congr_ae (rescaledCoefficient_apply_ae Ω A ε hε)]
  exact (eLpNorm_mono_measure (rescalePeriodic A ε) Measure.restrict_le_self).trans
    (eLpNorm_top_rescalePeriodic_le hε (Lp.aestronglyMeasurable A))

/-- Theorem 3.1, ellipticity at the microscopic scale: the original
lower and upper quadratic-form bounds hold outside one spatial null set
simultaneously for every strain. -/
theorem hasBounds_rescaledCoefficient_ae {α β : ℝ} (hA : HasFieldBounds α β A) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      HasBounds α β (rescaledCoefficient Ω A ε hε x) := by
  have hphysical : ∀ᵐ x ∂volume, HasBounds α β (rescalePeriodic A ε x) :=
    ae_rescalePeriodic (A := (A : PeriodicCell d → Elasticity d))
      (P := HasBounds α β) hε ((hasFieldBounds_iff_ae A).mp hA)
  filter_upwards [ae_restrict_of_ae hphysical, rescaledCoefficient_apply_ae Ω A ε hε]
    with x hx hrep
  rwa [hrep]

/-- Theorem 3.1 (`eq:two_scale_weak_form`): passing to the spatial L∞
class leaves the actual periodic weak form unchanged. -/
theorem spatialForm_rescaledCoefficient (u v : ZeroBoundaryH1 Ω) :
    spatialForm (rescaledCoefficient Ω A ε hε) u v =
      spatialForm (rescalePeriodic A ε) u v := by
  apply integral_congr_ae
  filter_upwards [rescaledCoefficient_apply_ae Ω A ε hε] with x hx
  rw [hx]

end KVApproximation.Homogenization
