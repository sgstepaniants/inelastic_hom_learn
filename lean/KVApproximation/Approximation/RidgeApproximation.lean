module

public import NeuralNetworkProofs.UniversalApproximation.Leshno.SmoothEngine
public import NeuralNetworkProofs.UniversalApproximation.Leshno.Ridge
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite ridge approximation on compact Euclidean sets
-/

public section

noncomputable section

open scoped InnerProductSpace
open UniversalApproximation.Leshno

namespace KVApproximation.Approximation

/-- Remark 4.3, scalar approximation ingredient: the closed continuous span
of translated and dilated activations gives the uniform ridge-approximation
predicate on every compact real set. -/
private theorem univariateDense_of_smooth {σ : ℝ → ℝ}
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σ) (hNonpoly : ¬ IsPolynomialFun σ) :
    UnivariateDense σ := by
  intro I hI
  have hspan : Sg σ I hSmooth.continuous ≤ T σ I := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩
    intro ε hε
    refine ⟨genFun σ a b, Submodule.subset_span ⟨(a, b), rfl⟩, ?_⟩
    intro x
    simpa [genFun, RCLike.inner_apply, mul_comm] using hε
  have hclosure := (Sg σ I hSmooth.continuous).topologicalClosure_minimal
    hspan (T_isClosed σ hI)
  rw [smooth_engine hSmooth hNonpoly I hI] at hclosure
  exact top_unique hclosure

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
  classical
  have hnp : ¬ IsPolynomialFun σ := by
    rintro ⟨p, hp⟩
    exact hNonpoly ⟨p, fun x => congrFun hp x⟩
  have hdense : DenselyApproximates σ :=
    denselyApproximates_of_forall_T_eq_top
      (fun K hK => ridge_density (univariateDense_of_smooth hSmooth hnp) K hK)
  obtain ⟨g, hg, herror⟩ := hdense K hK f hε
  obtain ⟨m, a, v, hsum⟩ := Submodule.mem_span_set'.mp hg
  let wb : Fin m → EuclideanSpace ℝ (Fin n) × ℝ :=
    fun j => (v j).property.choose
  have hwb (j : Fin m) : genFun σ (wb j).1 (wb j).2 = (v j).val :=
    (v j).property.choose_spec
  refine ⟨m, a, fun j => (wb j).1, fun j => (wb j).2, ?_⟩
  intro x
  have hx := congrFun hsum x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
  have heq : (∑ j : Fin m, a j * σ
      (⟪(wb j).1, (x : EuclideanSpace ℝ (Fin n))⟫_ℝ + (wb j).2)) = g x := by
    calc
      _ = ∑ j : Fin m, a j * ((v j).val x) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← hwb j]
        rfl
      _ = g x := hx
  rw [heq, abs_sub_comm]
  exact herror x

end KVApproximation.Approximation
