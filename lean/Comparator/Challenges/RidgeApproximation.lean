module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Finite ridge approximation with a smooth non-polynomial activation
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.Approximation

/-- Remark 4.3 (`rmk:fnm_admissible`), finite-dimensional approximation
ingredient: a smooth non-polynomial activation uniformly approximates any
continuous scalar target on any compact Euclidean input set by a finite ridge sum. -/
theorem exists_ridge_approximation {σ : ℝ → ℝ}
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σ x = p.eval x)
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (f : C(K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ a : Fin m → ℝ, ∃ w : Fin m → EuclideanSpace ℝ (Fin n),
      ∃ b : Fin m → ℝ, ∀ x : K,
        |(∑ j : Fin m, a j * σ (⟪w j, (x : EuclideanSpace ℝ (Fin n))⟫_ℝ + b j)) - f x| < ε := by
  sorry

end KVApproximation.Approximation
