module

public import KVApproximation.Homogenization.SpatialCoercivity
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Spatial stress bounds and weak equilibrium

The coefficient action preserves the Frobenius estimate with constant
one. Its L² stress pairing recovers the actual spatial weak form.
-/

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}
  (A : Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d))))

/-- Theorem 3.1, microscopic stress: the continuous stress map has
the actual coefficient-action representative. -/
theorem spatialStressL_apply_ae (u : ZeroBoundaryH1 Ω) :
    spatialStressL A u =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      action (A x) (VectorH1.symmetricGradientL Ω u.val x) := by
  exact (actionL d).coeFn_holder (r := 2) A (VectorH1.symmetricGradientL Ω u.val)

/-- Theorem 3.1, microscopic stress bound: Frobenius contraction and
the strain estimate retain constant one on arbitrary open domains. -/
theorem norm_spatialStressL_le (u : ZeroBoundaryH1 Ω) :
    ‖spatialStressL A u‖ ≤ ‖A‖ * ‖u‖ := by
  have hA : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)), ‖A x‖ ≤ ‖A‖ :=
    ae_le_lpNorm_exponent_top (Lp.memLp A)
  calc
    _ ≤ ‖A‖ * ‖VectorH1.symmetricGradientL Ω u.val‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [spatialStressL_apply_ae A u, hA] with x hx hAx
      rw [hx]
      exact (norm_action_le _ _).trans
        (mul_le_mul_of_nonneg_right hAx (norm_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((VectorH1.norm_symmetricGradientL_le u.val).trans (VectorH1.norm_gradientL_le u.val))
      (norm_nonneg A)

/-- Theorem 3.1, weak equilibrium: pairing the actual L² stress with
a Dirichlet strain is the spatial weak form. -/
theorem integral_spatialStressL_strain (u v : ZeroBoundaryH1 Ω) :
    (∫ x in (Ω : Set (PhysicalSpace d)),
      ⟪spatialStressL A u x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) =
        spatialForm A u v := by
  rw [← L2.inner_def]
  exact boundedSpatialForm_apply A u v

end KVApproximation.Homogenization
