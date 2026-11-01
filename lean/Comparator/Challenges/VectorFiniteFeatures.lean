module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Vector approximation through finitely many observations
-/

public section

namespace KVApproximation.Approximation

/-- Remark 4.3, finite-feature reduction: a separating family of continuous
real observations approximates every continuous Euclidean-valued target on a
compact space through finitely many observations, in the Euclidean norm. -/
theorem exists_vector_finite_feature_approximation
    {X I : Type*} [TopologicalSpace X] [CompactSpace X]
    (φ : I → C(X, ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ i : I, φ i x ≠ φ i y)
    (n : ℕ) (f : C(X, EuclideanSpace ℝ (Fin n))) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset I, ∃ g : C((s → ℝ), EuclideanSpace ℝ (Fin n)), ∀ x : X,
      ‖g (fun i : s => φ i x) - f x‖ < ε := by
  sorry

end KVApproximation.Approximation
