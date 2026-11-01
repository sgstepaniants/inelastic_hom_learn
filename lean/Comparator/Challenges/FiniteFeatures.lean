module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Approximation by finitely many separating features
-/

public section

namespace KVApproximation.Approximation

/-- Remark 4.3, finite-feature reduction: a point-separating family of
continuous real features uniformly approximates every continuous scalar target
on a compact space through a continuous function of finitely many features. -/
theorem exists_finite_feature_approximation
    {X I : Type*} [TopologicalSpace X] [CompactSpace X]
    (φ : I → C(X, ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ i : I, φ i x ≠ φ i y)
    (f : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset I, ∃ g : C((s → ℝ), ℝ), ∀ x : X,
      |g (fun i : s => φ i x) - f x| < ε := by
  sorry

end KVApproximation.Approximation
