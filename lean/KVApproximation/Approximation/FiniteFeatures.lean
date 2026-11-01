module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Uniform approximation by finitely many features
-/

public section

noncomputable section

namespace KVApproximation.Approximation

/-- Remark 4.3, finite-feature reduction: restriction between finite
coordinate spaces is continuous on the whole coordinate space. -/
private def restrictFeatures {I : Type*} {s t : Finset I} (hst : s ⊆ t) :
    C((t → ℝ), (s → ℝ)) where
  toFun x i := x ⟨i.val, hst i.property⟩
  continuous_toFun := continuous_pi fun i : s =>
    continuous_apply (⟨i.val, hst i.property⟩ : t)

/-- Remark 4.3, finite-feature reduction: continuous functions of finitely
many selected features form a unital real algebra. -/
private def finiteFeatureAlgebra {X I : Type*} [TopologicalSpace X]
    (φ : I → C(X, ℝ)) : Subalgebra ℝ C(X, ℝ) where
  carrier := {f | ∃ s : Finset I, ∃ g : C((s → ℝ), ℝ),
    ∀ x : X, f x = g (fun i : s => φ i x)}
  algebraMap_mem' r := ⟨∅, ContinuousMap.const _ r, fun _ => rfl⟩
  add_mem' := by
    classical
    rintro a b ⟨s, f, hf⟩ ⟨t, g, hg⟩
    refine ⟨s ∪ t, f.comp (restrictFeatures Finset.subset_union_left) +
      g.comp (restrictFeatures Finset.subset_union_right), ?_⟩
    intro x
    change a x + b x = f (fun i : s => φ i x) + g (fun i : t => φ i x)
    rw [hf, hg]
  mul_mem' := by
    classical
    rintro a b ⟨s, f, hf⟩ ⟨t, g, hg⟩
    refine ⟨s ∪ t, f.comp (restrictFeatures Finset.subset_union_left) *
      g.comp (restrictFeatures Finset.subset_union_right), ?_⟩
    intro x
    change a x * b x = f (fun i : s => φ i x) * g (fun i : t => φ i x)
    rw [hf, hg]

/-- Remark 4.3, finite-feature reduction: each original feature belongs
to the algebra by taking one coordinate. -/
private theorem feature_mem_finiteFeatureAlgebra
    {X I : Type*} [TopologicalSpace X] (φ : I → C(X, ℝ)) (i : I) :
    φ i ∈ finiteFeatureAlgebra φ := by
  classical
  refine ⟨{i}, ⟨fun x => x ⟨i, Finset.mem_singleton_self i⟩,
    continuous_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset I))⟩, ?_⟩
  intro x
  rfl

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
  have hA : (finiteFeatureAlgebra φ).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    exact ⟨(φ i : X → ℝ), ⟨φ i, feature_mem_finiteFeatureAlgebra φ i, rfl⟩, hi⟩
  obtain ⟨q, hq⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      (finiteFeatureAlgebra φ) hA f f.continuous ε hε
  obtain ⟨s, g, hg⟩ := q.property
  refine ⟨s, g, ?_⟩
  intro x
  simpa only [Real.norm_eq_abs, hg x] using hq x

end KVApproximation.Approximation
