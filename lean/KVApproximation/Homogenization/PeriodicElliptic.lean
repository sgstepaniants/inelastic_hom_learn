module

public import KVApproximation.Homogenization.RescaledFieldProperties
public import KVApproximation.Homogenization.SpatialCoercivity

/-!
# Periodic elliptic equilibrium and prepared initial data
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

private theorem rescaled_lower_bound (A : CoerciveField d) (ε : ℝ) (hε : ε ≠ 0) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)), ∀ e : Symmetric d,
      A.lower * ‖e‖ ^ 2 ≤ ⟪e, action (rescaledCoefficient Ω A.field ε hε x) e⟫_ℝ := by
  exact (hasBounds_rescaledCoefficient_ae Ω A.field ε hε A.bounds).mono
    fun _ hx e => (hx e).1

/-- Theorem 3.1, static microscopic problems: every positive scale
and L² load admit a unique weak equilibrium for the actual periodic field. -/
theorem periodic_elliptic_exists_unique (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) (f : SpatialL2 Ω) :
    ∃! u : ZeroBoundaryH1 Ω, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic A.field ε) u v = loadPairing f v := by
  have h := elliptic_exists_unique (d := d) (Ω := Ω) (α := A.lower)
    (rescaledCoefficient Ω A.field ε hε.ne') hΩ A.lower_pos
    (rescaled_lower_bound (Ω := Ω) A ε hε.ne') f
  simpa only [spatialForm_rescaledCoefficient] using h

/-- Theorem 3.1, uniform static estimate: one positive constant bounds
all microscopic equilibria in full H¹, independently of scale and load. -/
theorem periodic_elliptic_uniform_bound (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ (f : SpatialL2 Ω) (u : ZeroBoundaryH1 Ω),
      (∀ v : ZeroBoundaryH1 Ω,
        spatialForm (rescalePeriodic A.field ε) u v = loadPairing f v) →
      ‖u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hK⟩ := ZeroBoundaryH1.exists_korn_constant hΩ
  refine ⟨C ^ 2 / A.lower, div_pos (pow_pos hC 2) A.lower_pos, ?_⟩
  intro ε hε f u hu
  apply norm_elliptic_solution_le (d := d) (Ω := Ω)
    (rescaledCoefficient Ω A.field ε hε.ne') A.lower_pos hC
    (rescaled_lower_bound (Ω := Ω) A ε hε.ne') hK f u
  intro v
  simpa only [spatialForm_rescaledCoefficient] using hu v

/-- Theorem 3.1, admissible initial conditions: every fixed L² load
generates an elastically prepared family with a scale-independent H¹ bound. -/
theorem exists_preparedInitialFamily (E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (g₀ : SpatialL2 Ω) :
    ∃ u₀ : ℝ → ZeroBoundaryH1 Ω, IsPreparedInitialFamily E g₀ u₀ ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ‖u₀ ε‖ ≤ C * ‖g₀‖ := by
  classical
  have hex (ε : ℝ) : ∃ u : ZeroBoundaryH1 Ω, 0 < ε → ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic E.field ε) u v = loadPairing g₀ v := by
    by_cases hε : 0 < ε
    · obtain ⟨u, hu, _⟩ := periodic_elliptic_exists_unique E hΩ ε hε g₀
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h => False.elim (hε h)⟩
  choose u₀ hu₀ using hex
  have hprepared : IsPreparedInitialFamily E g₀ u₀ := hu₀
  obtain ⟨C, hC, hbound⟩ := periodic_elliptic_uniform_bound E hΩ
  exact ⟨u₀, hprepared, C, hC, fun ε hε => hbound ε hε g₀ (u₀ ε) (hprepared ε hε)⟩

end KVApproximation.Homogenization
