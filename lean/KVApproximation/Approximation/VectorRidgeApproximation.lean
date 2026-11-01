module

public import KVApproximation.Approximation.RidgeApproximation
public import KVApproximation.Approximation.VectorFiniteFeatures
public import Mathlib.Data.Fintype.BigOperators

/-!
# Vector-valued finite ridge approximation

Concatenating the scalar approximants gives one finite hidden layer and a
linear vector output, with error measured in the Euclidean norm.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace KVApproximation.Approximation

/-- Remark 4.3, output error: the Euclidean norm is bounded by the sum of
the absolute coordinate errors, including an empty coordinate type. -/
private theorem euclidean_norm_le_sum_abs {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) : ‖v‖ ≤ ∑ i : Fin n, |v i| := by
  have hv : v = ∑ i : Fin n, PiLp.single 2 i (v i) := by
    apply PiLp.ext
    intro j
    simp [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
  calc
    ‖v‖ = ‖∑ i : Fin n, PiLp.single 2 i (v i)‖ := congrArg norm hv
    _ ≤ ∑ i : Fin n, ‖(PiLp.single 2 i (v i) : EuclideanSpace ℝ (Fin n))‖ :=
      norm_sum_le Finset.univ (fun i => (PiLp.single 2 i (v i) : EuclideanSpace ℝ (Fin n)))
    _ = ∑ i : Fin n, |v i| := by simp only [PiLp.norm_single, Real.norm_eq_abs]

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
  classical
  let δ := ε / ((output : ℝ) + 1)
  have hden : 0 < (output : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let fj (j : Fin output) : C(K, ℝ) :=
    ⟨fun x => f x j,
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin output => ℝ) j).continuous.comp f.continuous⟩
  have hex (j : Fin output) :=
    exists_ridge_approximation hSmooth hNonpoly input K hK (fj j) hδ
  choose m a w b herror using hex
  let S := Σ j : Fin output, Fin (m j)
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let A (j : Fin (Fintype.card S)) : EuclideanSpace ℝ (Fin output) :=
    PiLp.single 2 (e j).1 (a (e j).1 (e j).2)
  let W (j : Fin (Fintype.card S)) := w (e j).1 (e j).2
  let B (j : Fin (Fintype.card S)) := b (e j).1 (e j).2
  let q (x : K) : EuclideanSpace ℝ (Fin output) :=
    ∑ j : Fin (Fintype.card S),
      σ (⟪W j, (x : EuclideanSpace ℝ (Fin input))⟫_ℝ + B j) • A j
  have hsum (x : K) : q x = ∑ j : Fin output, ∑ t : Fin (m j),
      σ (⟪w j t, (x : EuclideanSpace ℝ (Fin input))⟫_ℝ + b j t) •
        PiLp.single 2 j (a j t) := by
    exact (e.sum_comp (fun z : S =>
      σ (⟪w z.1 z.2, (x : EuclideanSpace ℝ (Fin input))⟫_ℝ + b z.1 z.2) •
        (PiLp.single 2 z.1 (a z.1 z.2) : EuclideanSpace ℝ (Fin output)))).trans
      (Fintype.sum_sigma _)
  have hcoordinate (x : K) (j : Fin output) :
      q x j = ∑ t : Fin (m j), a j t *
        σ (⟪w j t, (x : EuclideanSpace ℝ (Fin input))⟫_ℝ + b j t) := by
    rw [hsum]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul, PiLp.single_apply, mul_ite, mul_zero]
    rw [Finset.sum_eq_single j]
    · simp only [ite_true]
      apply Finset.sum_congr rfl
      intro t ht
      exact mul_comm _ _
    · intro i hi hij
      simp [Ne.symm hij]
    · simp
  have hbudget : (output : ℝ) * δ < ε := calc
    (output : ℝ) * δ < ((output : ℝ) + 1) * δ :=
      mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := mul_div_cancel₀ ε hden.ne'
  refine ⟨Fintype.card S, A, W, B, fun x => ?_⟩
  change ‖q x - f x‖ < ε
  calc
    ‖q x - f x‖ ≤ ∑ j : Fin output, |(q x - f x) j| :=
      euclidean_norm_le_sum_abs _
    _ ≤ ∑ _j : Fin output, δ := by
      apply Finset.sum_le_sum
      intro j hj
      change |q x j - f x j| ≤ δ
      rw [hcoordinate]
      exact (herror j x).le
    _ = (output : ℝ) * δ := by simp
    _ < ε := hbudget

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
  classical
  obtain ⟨s, g, hfinite⟩ :=
    exists_vector_finite_feature_approximation φ hsep output f (half_pos hε)
  let features := Fintype.card s
  let e : Fin features ≃ s := (Fintype.equivFin s).symm
  let obs (i : Fin features) : I := (e i).val
  let Y : C(X, EuclideanSpace ℝ (Fin features)) :=
    ⟨fun x => WithLp.toLp 2 (fun i => φ (obs i) x),
      (PiLp.continuous_toLp 2 (fun _ : Fin features => ℝ)).comp
        (continuous_pi fun i => (φ (obs i)).continuous)⟩
  let G : C(EuclideanSpace ℝ (Fin features), EuclideanSpace ℝ (Fin output)) :=
    ⟨fun z => g (fun i : s => z (e.symm i)),
      g.continuous.comp (continuous_pi fun i : s =>
        (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin features => ℝ) (e.symm i)).continuous)⟩
  have hGY (x : X) : G (Y x) = g (fun i : s => φ i x) := by
    change g (fun i : s => φ (e (e.symm i)) x) = _
    simp only [e.apply_symm_apply]
  let K := Set.range Y
  have hK : IsCompact K := isCompact_range Y.continuous
  let target : C(K, EuclideanSpace ℝ (Fin output)) :=
    ⟨fun z => G z.val, G.continuous.comp continuous_subtype_val⟩
  obtain ⟨width, a, w, b, herror⟩ :=
    exists_vector_ridge_approximation hSmooth hNonpoly features output K hK
      target (half_pos hε)
  have hinner (j : Fin width) (x : X) :
      ⟪w j, Y x⟫_ℝ = ∑ i : Fin features, w j i * φ (obs i) x := by
    simp [PiLp.inner_apply, RCLike.inner_apply, Y, mul_comm]
  refine ⟨features, obs, width, a, (fun j i => w j i), b, fun x => ?_⟩
  have hridge := herror ⟨Y x, ⟨x, rfl⟩⟩
  change ‖(∑ j : Fin width, σ (⟪w j, Y x⟫_ℝ + b j) • a j) - G (Y x)‖ < ε / 2 at hridge
  simp only [hinner] at hridge
  have hfeature : ‖G (Y x) - f x‖ < ε / 2 := by
    rw [hGY]
    exact hfinite x
  calc
    _ ≤ ‖(∑ j : Fin width,
          σ ((∑ i : Fin features, w j i * φ (obs i) x) + b j) • a j) - G (Y x)‖ +
        ‖G (Y x) - f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hridge hfeature
    _ = ε := add_halves ε

end KVApproximation.Approximation
