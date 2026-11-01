module

public import KVApproximation.Homogenization.SpatialOperators
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Spatial ellipticity and weak equilibrium
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}
  (A : Lp (Elasticity d) ⊤ (volume.restrict (Ω : Set (PhysicalSpace d))))

/-- Theorem 3.1, weak elliptic formulation: bounded coefficients and
L² strains give an integrable energy pairing on any open domain. -/
theorem integrable_spatialForm (u v : ZeroBoundaryH1 Ω) :
    Integrable (fun x => ⟪symmetricGradient u x,
      action (A x) (symmetricGradient v x)⟫_ℝ)
        (volume.restrict (Ω : Set (PhysicalSpace d))) := by
  sorry

/-- Theorem 3.1, static elliptic problems: the constructed continuous
form equals the spatial weak form in the paper. -/
theorem boundedSpatialForm_apply (u v : ZeroBoundaryH1 Ω) :
    boundedSpatialForm A u v = spatialForm A u v := by
  sorry

/-- Theorem 3.1, static elliptic problems: major coefficient symmetry
gives symmetry of the spatial form. -/
theorem boundedSpatialForm_symmetric (u v : ZeroBoundaryH1 Ω) :
    boundedSpatialForm A u v = boundedSpatialForm A v u := by
  sorry

/-- Theorem 3.1, spatial coercivity: pointwise ellipticity bounds the
integrated strain energy with the same coefficient. -/
theorem spatialForm_lower_bound {α : ℝ}
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      ∀ e : Symmetric d, α * ‖e‖ ^ 2 ≤ ⟪e, action (A x) e⟫_ℝ)
    (u : ZeroBoundaryH1 Ω) :
    α * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 ≤ spatialForm A u u := by
  sorry

/-- Theorem 3.1, static elliptic problems: Korn's inequality turns
pointwise ellipticity into coercivity in the full Dirichlet H¹ norm. -/
theorem boundedSpatialForm_isCoercive
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)),
      ∀ e : Symmetric d, α * ‖e‖ ^ 2 ≤ ⟪e, action (A x) e⟫_ℝ) :
    IsCoercive (E := ZeroBoundaryH1 Ω) (boundedSpatialForm (Ω := Ω) A) := by
  sorry

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
  sorry

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
  sorry

end KVApproximation.Homogenization
