module

public import KVApproximation.Homogenization.ConstantSpatialFormProperties
public import KVApproximation.Homogenization.SpatialCoercivity

/-!
# Coercivity of constant spatial tensors

The constant coefficient has its actual L∞ representative. The spatial Korn
estimate transfers its positive quadratic lower bound to the Dirichlet norm.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Theorem 3.1, viscous norm bound: evaluating a coercive dual form
on its own displacement gives a quantitative lower operator bound. -/
private theorem exists_dual_bound_of_coercive {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H, ‖u‖ ≤ C * ‖B u‖ := by
  obtain ⟨α, hα, hbound⟩ := hB
  refine ⟨α⁻¹, inv_pos.mpr hα, fun u => ?_⟩
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    exact mul_nonneg (inv_nonneg.mpr hα.le) (norm_nonneg _)
  · have hn : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    have he : (α * ‖u‖) * ‖u‖ ≤ ‖B u‖ * ‖u‖ :=
      (hbound u).trans ((le_abs_self _).trans ((B u).le_opNorm u))
    have he' := (mul_le_mul_iff_left₀ hn).mp he
    have h := mul_le_mul_of_nonneg_left he' (inv_nonneg.mpr hα.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul] using h

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance ConstantSpatialCoercivity.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance ConstantSpatialCoercivity.instNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω) := inferInstance

local instance ConstantSpatialCoercivity.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Theorem 3.1, homogenized spatial coercivity: positive definiteness
of a constant tensor and the Dirichlet Korn estimate give coercivity in the
actual H¹₀ norm on every bounded open domain. -/
theorem constantSpatialFormL_isCoercive (A : Elasticity d) (hA : PositiveDefinite A)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    IsCoercive (constantSpatialFormL (Ω := Ω) A) := by
  obtain ⟨α, hα, hbound⟩ := hA
  let μ := volume.restrict (Ω : Set (PhysicalSpace d))
  have hm : MemLp (fun _ : PhysicalSpace d => A) ⊤ μ := memLp_top_const A
  let B := hm.toLp (fun _ : PhysicalSpace d => A)
  have hB : B =ᵐ[μ] fun _ => A := hm.coeFn_toLp
  have hBlower : ∀ᵐ x ∂μ, ∀ e : Symmetric d,
      α * ‖e‖ ^ 2 ≤ ⟪e, action (B x) e⟫_ℝ := by
    filter_upwards [hB] with x hx
    simpa only [hx] using hbound
  have heq : constantSpatialFormL (Ω := Ω) A = boundedSpatialForm (Ω := Ω) B := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    rw [constantSpatialFormL_apply, boundedSpatialForm_apply]
    apply integral_congr_ae
    filter_upwards [hB] with x hx
    rw [hx]
  rw [heq]
  exact boundedSpatialForm_isCoercive B hΩ hα hBlower

/-- Theorem 3.1, finite-time uniqueness: a positive constant tensor
controls the actual displacement norm by its spatial dual norm. -/
theorem exists_constantSpatialFormL_norm_bound (A : Elasticity d) (hA : PositiveDefinite A)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ZeroBoundaryH1 Ω,
      ‖u‖ ≤ C * ‖constantSpatialFormL (Ω := Ω) A u‖ := by
  exact exists_dual_bound_of_coercive (constantSpatialFormL (Ω := Ω) A)
    (constantSpatialFormL_isCoercive A hA hΩ)

end KVApproximation.Homogenization
