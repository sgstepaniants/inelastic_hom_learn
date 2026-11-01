module

public import KVApproximation.Homogenization.StaticWeakProblem
public import KVApproximation.Homogenization.StaticCellOperators
public import KVApproximation.Analysis.VectorSobolevFields

public section

open MeasureTheory TopologicalSpace Filter
open KVApproximation.Analysis KVApproximation.Tensor
open scoped Topology

namespace KVApproximation.Homogenization

/-- Theorem 3.1, static periodic homogenization in the Laplace-domain
argument: microscopic equilibria converge weakly in H¹₀ and strongly in
L² to the unique equilibrium of the actual effective cell form. -/
theorem periodic_elliptic_homogenization {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A : CoerciveField d) (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (f : SpatialL2 Ω) (u : ℝ → ZeroBoundaryH1 Ω)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic A.field ε) (u ε) v = loadPairing f v) :
    ∃ u₀ : ZeroBoundaryH1 Ω,
      (∀ v : ZeroBoundaryH1 Ω,
        (∫ x in (Ω : Set (PhysicalSpace d)),
          effectiveForm A (symmetricGradient u₀ x) (symmetricGradient v x)) =
            loadPairing f v) ∧
      (∀ w : ZeroBoundaryH1 Ω,
        (∀ v : ZeroBoundaryH1 Ω,
          (∫ x in (Ω : Set (PhysicalSpace d)),
            effectiveForm A (symmetricGradient w x) (symmetricGradient v x)) =
              loadPairing f v) → w = u₀) ∧
      (∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ u₀))) ∧
      Tendsto (fun ε => VectorH1.valueL Ω (u ε).val) (𝓝[>] (0 : ℝ))
        (𝓝 (VectorH1.valueL Ω u₀.val)) := by
  sorry

/-- Theorem 3.1, static limit identification: every weak H¹₀ limit
of equilibria along positive vanishing scales solves the effective equation. -/
theorem periodic_elliptic_weak_limit {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A : CoerciveField d) (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (f : SpatialL2 Ω) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hpos : ∀ n, 0 < ε n) (u : ℕ → ZeroBoundaryH1 Ω)
    (hu : ∀ n, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic A.field (ε n)) (u n) v = loadPairing f v)
    (uLim : ZeroBoundaryH1 Ω)
    (hweak : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ uLim))) :
    ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm A (symmetricGradient uLim x) (symmetricGradient v x)) =
          loadPairing f v := by
  sorry

end KVApproximation.Homogenization
