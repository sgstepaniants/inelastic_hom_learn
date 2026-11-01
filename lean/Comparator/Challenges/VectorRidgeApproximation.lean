module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Algebra.Polynomial.Eval.Defs

public section

noncomputable section

open scoped InnerProductSpace

namespace KVApproximation.Approximation

/-- Remark 4.3 (`rmk:fnm_admissible`), vector output: one finite ridge sum
approximates a continuous Euclidean-valued target in the Euclidean norm. -/
theorem exists_vector_ridge_approximation {σ : ℝ → ℝ}
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σ x = p.eval x)
    (input output : ℕ) (K : Set (EuclideanSpace ℝ (Fin input))) (hK : IsCompact K)
    (f : C(K, EuclideanSpace ℝ (Fin output))) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ a : Fin m → EuclideanSpace ℝ (Fin output),
      ∃ w : Fin m → EuclideanSpace ℝ (Fin input), ∃ b : Fin m → ℝ,
        ∀ x : K, ‖(∑ j : Fin m,
          σ (⟪w j, (x : EuclideanSpace ℝ (Fin input))⟫_ℝ + b j) • a j) - f x‖ < ε := by
  sorry

/-- Remark 4.3, finite observations and ridge approximation: a separating
family of continuous scalar observations admits a finite ridge approximant
for every continuous Euclidean-valued target on a compact space. -/
theorem exists_finite_feature_ridge_approximation
    {X I : Type*} [TopologicalSpace X] [CompactSpace X]
    (φ : I → C(X, ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ i : I, φ i x ≠ φ i y)
    {σ : ℝ → ℝ} (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σ x = p.eval x)
    (output : ℕ) (f : C(X, EuclideanSpace ℝ (Fin output)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ features : ℕ, ∃ obs : Fin features → I,
      ∃ width : ℕ, ∃ a : Fin width → EuclideanSpace ℝ (Fin output),
        ∃ w : Matrix (Fin width) (Fin features) ℝ, ∃ b : Fin width → ℝ,
          ∀ x : X, ‖(∑ j : Fin width,
            σ ((∑ i : Fin features, w j i * φ (obs i) x) + b j) • a j) - f x‖ < ε := by
  sorry

end KVApproximation.Approximation
