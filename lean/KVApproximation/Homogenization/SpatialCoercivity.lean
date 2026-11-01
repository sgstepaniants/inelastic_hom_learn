module

public import KVApproximation.Homogenization.SpatialFormIdentities
public import KVApproximation.Analysis.DirichletKorn
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Spatial ellipticity and weak equilibrium
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

private theorem unique_for_coercive_form {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B) (f : H →L[ℝ] ℝ) :
    ∃! u : H, ∀ v : H, B u v = f v := by
  let L := hB.continuousLinearEquivOfBilin
  let g := (InnerProductSpace.toDual ℝ H).symm f
  have hL (u v : H) : ⟪L u, v⟫_ℝ = B u v := hB.continuousLinearEquivOfBilin_apply u v
  have hg (v : H) : ⟪g, v⟫_ℝ = f v := InnerProductSpace.toDual_symm_apply
  refine ⟨L.symm g, ?_, ?_⟩
  · intro v
    rw [← hL, L.apply_symm_apply, hg]
  · intro w hw
    apply L.injective
    apply ext_inner_right ℝ
    intro v
    rw [L.apply_symm_apply, hL, hw, hg]

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}
  (A : Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d))))

/-- Theorem 3.1, spatial coercivity: pointwise ellipticity bounds the
integrated strain energy with the same coefficient. -/
theorem spatialForm_lower_bound {α : ℝ}
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      ∀ e : Symmetric d, α * ‖e‖ ^ 2 ≤ ⟪e, action (A x) e⟫_ℝ)
    (u : ZeroBoundaryH1 Ω) :
    α * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 ≤ spatialForm A u u := by
  have hi := (symmetricGradient_memLp u).norm.integrable_sq
  have he : (∫ x in (Ω : Set (PhysicalSpace d)), ‖symmetricGradient u x‖ ^ 2) =
      ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [symmetricGradientL_apply_ae u] with x hx
    rw [hx]
  have h := integral_mono_ae (hi.const_mul α) (integrable_spatialForm A u u)
    (hA.mono fun x hx => hx (symmetricGradient u x))
  simpa only [integral_const_mul, he, spatialForm] using h

private theorem coercivity_bound {α C : ℝ} (hα : 0 < α) (hC : 0 < C)
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      ∀ e : Symmetric d, α * ‖e‖ ^ 2 ≤ ⟪e, action (A x) e⟫_ℝ)
    (hK : ∀ v : ZeroBoundaryH1 Ω,
      ‖v‖ ≤ C * ‖VectorH1.symmetricGradientL Ω v.val‖)
    (u : ZeroBoundaryH1 Ω) :
    (α / C ^ 2) * ‖u‖ ^ 2 ≤ spatialForm A u u := by
  have hs := pow_le_pow_left₀ (norm_nonneg u) (hK u) 2
  rw [mul_pow] at hs
  calc
    (α / C ^ 2) * ‖u‖ ^ 2 ≤
        (α / C ^ 2) * (C ^ 2 * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hα.le (sq_nonneg C))
    _ = α * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 := by
      rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hC.ne')]
    _ ≤ spatialForm A u u := spatialForm_lower_bound A hA u

/-- Theorem 3.1, static elliptic problems: Korn's inequality turns
pointwise ellipticity into coercivity in the full Dirichlet H¹ norm. -/
theorem boundedSpatialForm_isCoercive
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      ∀ e : Symmetric d, α * ‖e‖ ^ 2 ≤ ⟪e, action (A x) e⟫_ℝ) :
    IsCoercive (E := ZeroBoundaryH1 Ω) (boundedSpatialForm (Ω := Ω) A) := by
  obtain ⟨C, hC, hK⟩ := ZeroBoundaryH1.exists_korn_constant hΩ
  refine ⟨α / C ^ 2, div_pos hα (pow_pos hC 2), fun u => ?_⟩
  rw [boundedSpatialForm_apply]
  simpa only [pow_two, mul_assoc] using coercivity_bound A hα hC hA hK u

private theorem spatialLoadL_apply (f : SpatialL2 Ω) (v : ZeroBoundaryH1 Ω) :
    spatialLoadL f v = loadPairing f v := by
  rw [loadPairing_eq_inner]
  rfl

/-- Theorem 3.1, admissible initial data and transformed static
problems: every square-integrable load has one weak equilibrium. -/
theorem elliptic_exists_unique
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      ∀ e : Symmetric d, α * ‖e‖ ^ 2 ≤ ⟪e, action (A x) e⟫_ℝ)
    (f : SpatialL2 Ω) :
    ∃! u : ZeroBoundaryH1 Ω, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm A u v = loadPairing f v := by
  have hc := boundedSpatialForm_isCoercive (d := d) (Ω := Ω) (α := α) A hΩ hα hA
  obtain ⟨u, hu, huniq⟩ := unique_for_coercive_form (H := ZeroBoundaryH1 Ω)
    (boundedSpatialForm (Ω := Ω) A) hc (spatialLoadL (Ω := Ω) f)
  refine ⟨u, ?_, ?_⟩
  · intro v
    simpa only [boundedSpatialForm_apply, spatialLoadL_apply] using hu v
  · intro w hw
    apply huniq w
    intro v
    simpa only [boundedSpatialForm_apply, spatialLoadL_apply] using hw v

/-- Theorem 3.1, uniform static estimate: the solution norm depends
only on the ellipticity lower bound, a domain Korn constant and the load. -/
theorem norm_elliptic_solution_le {α C : ℝ} (hα : 0 < α) (hC : 0 < C)
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      ∀ e : Symmetric d, α * ‖e‖ ^ 2 ≤ ⟪e, action (A x) e⟫_ℝ)
    (hK : ∀ v : ZeroBoundaryH1 Ω,
      ‖v‖ ≤ C * ‖VectorH1.symmetricGradientL Ω v.val‖)
    (f : SpatialL2 Ω) (u : ZeroBoundaryH1 Ω)
    (hu : ∀ v : ZeroBoundaryH1 Ω, spatialForm A u v = loadPairing f v) :
    ‖u‖ ≤ (C ^ 2 / α) * ‖f‖ := by
  have hb := coercivity_bound A hα hC hA hK u
  rw [hu u] at hb
  have he : (α / C ^ 2) * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ :=
    hb.trans ((le_abs_self _).trans (abs_loadPairing_le f u))
  by_cases hz : u = 0
  · calc
      ‖u‖ = 0 := norm_eq_zero.mpr hz
      _ ≤ _ := mul_nonneg (div_nonneg (sq_nonneg C) hα.le) (norm_nonneg f)
  · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hz
    have hl : (α / C ^ 2) * ‖u‖ ≤ ‖f‖ :=
      (mul_le_mul_iff_left₀ hn).mp (by simpa only [pow_two, mul_assoc] using he)
    calc
      ‖u‖ = (C ^ 2 / α) * ((α / C ^ 2) * ‖u‖) := by
        field_simp
      _ ≤ (C ^ 2 / α) * ‖f‖ :=
        mul_le_mul_of_nonneg_left hl (div_nonneg (sq_nonneg C) hα.le)

end KVApproximation.Homogenization
