module

public import KVApproximation.Approximation.FiniteFeatures
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Vector approximation through finitely many observations
-/

public section

noncomputable section

namespace KVApproximation.Approximation

/-- Remark 4.3, finite-feature error: the Euclidean norm is at most the
sum of the absolute coordinate errors. -/
private theorem norm_le_sum_abs {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ≤ ∑ i : Fin n, |v i| := by
  have hv : v = ∑ i : Fin n, PiLp.single 2 i (v i) := by
    apply PiLp.ext
    intro j
    simp [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
  calc
    ‖v‖ = ‖∑ i : Fin n, PiLp.single 2 i (v i)‖ := congrArg norm hv
    _ ≤ ∑ i : Fin n, ‖(PiLp.single 2 i (v i) : EuclideanSpace ℝ (Fin n))‖ :=
      norm_sum_le Finset.univ (fun i => (PiLp.single 2 i (v i) : EuclideanSpace ℝ (Fin n)))
    _ = ∑ i : Fin n, |v i| := by simp only [PiLp.norm_single, Real.norm_eq_abs]

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
  classical
  let δ := ε / ((n : ℝ) + 1)
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let fj (j : Fin n) : C(X, ℝ) :=
    ⟨fun x => f x j,
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous.comp f.continuous⟩
  have hex (j : Fin n) := exists_finite_feature_approximation φ hsep (fj j) hδ
  choose s g herror using hex
  let S : Finset I := Finset.univ.biUnion s
  have hsub (j : Fin n) : s j ⊆ S := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hi⟩
  let restrict (j : Fin n) : C((S → ℝ), (s j → ℝ)) :=
    ⟨fun x i => x ⟨i.val, hsub j i.property⟩,
      continuous_pi fun i : s j => continuous_apply (⟨i.val, hsub j i.property⟩ : S)⟩
  let G : C((S → ℝ), EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x => WithLp.toLp 2 (fun j => g j (restrict j x)),
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.continuous.comp
        (continuous_pi fun j => (g j).continuous.comp (restrict j).continuous)⟩
  have hbudget : (n : ℝ) * δ < ε := calc
    (n : ℝ) * δ < ((n : ℝ) + 1) * δ :=
      mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := mul_div_cancel₀ ε hden.ne'
  refine ⟨S, G, fun x => ?_⟩
  calc
    ‖G (fun i : S => φ i x) - f x‖ ≤
        ∑ j : Fin n, |(G (fun i : S => φ i x) - f x) j| := norm_le_sum_abs _
    _ ≤ ∑ _j : Fin n, δ := by
      apply Finset.sum_le_sum
      intro j hj
      change |g j (fun i : s j => φ i x) - f x j| ≤ δ
      exact (herror j x).le
    _ = (n : ℝ) * δ := by simp
    _ < ε := hbudget

end KVApproximation.Approximation
