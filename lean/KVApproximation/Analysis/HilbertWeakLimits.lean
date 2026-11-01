module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Norm bounds under weak Hilbert-space convergence
-/

public section

open Filter
open scoped Topology NNReal InnerProductSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, uniform bounds in the limit: an eventual Hilbert-norm
bound passes through weak convergence along every nontrivial filter. -/
theorem norm_le_of_weak_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {I : Type*} {l : Filter I} [NeBot l]
    (u : I → H) (uLim : H) {C : ℝ}
    (hu : ∀ ℓ : H →L[ℝ] ℝ, Tendsto (fun i => ℓ (u i)) l (𝓝 (ℓ uLim)))
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C) : ‖uLim‖ ≤ C := by
  have hC : 0 ≤ C := by
    obtain ⟨i, hi⟩ := hbound.exists
    exact (norm_nonneg (u i)).trans hi
  have hpair : innerSL ℝ uLim uLim ≤ ‖uLim‖ * C := by
    apply le_of_tendsto (hu (innerSL ℝ uLim))
    filter_upwards [hbound] with i hi
    calc
      innerSL ℝ uLim (u i) ≤ ‖innerSL ℝ uLim (u i)‖ := le_abs_self _
      _ ≤ ‖innerSL ℝ uLim‖ * ‖u i‖ := (innerSL ℝ uLim).le_opNorm _
      _ = ‖uLim‖ * ‖u i‖ := by rw [innerSL_apply_norm]
      _ ≤ ‖uLim‖ * C := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
  rw [innerSL_apply_apply, real_inner_self_eq_norm_sq] at hpair
  by_cases hz : ‖uLim‖ = 0
  · simpa only [hz] using hC
  · exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg uLim) (Ne.symm hz))).mp
      (by simpa only [pow_two] using hpair)

/-- Theorem 3.1, Green-operator construction: a pointwise weak limit
of uniformly bounded linear operators is a bounded linear operator with
the same norm bound. Neither space needs to be complete. -/
theorem exists_continuousLinearMap_of_weak_tendsto
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {I : Type*} {l : Filter I} [NeBot l]
    (A : I → E →L[ℝ] H) (f : E → H) {C : ℝ}
    (hweak : ∀ x : E, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (A i x)) l (𝓝 (ℓ (f x))))
    (hbound : ∀ᶠ i in l, ‖A i‖ ≤ C) :
    ∃ B : E →L[ℝ] H, (∀ x : E, B x = f x) ∧ ‖B‖ ≤ C := by
  have hC : 0 ≤ C := by
    obtain ⟨i, hi⟩ := hbound.exists
    exact (norm_nonneg (A i)).trans hi
  have hnorm (x : E) : ‖f x‖ ≤ C * ‖x‖ := by
    apply norm_le_of_weak_tendsto (fun i => A i x) (f x) (hweak x)
    filter_upwards [hbound] with i hi
    exact (A i).le_of_opNorm_le hi x
  let B₀ : E →ₗ[ℝ] H :=
    { toFun := f
      map_add' := by
        intro x y
        apply ext_inner_left ℝ
        intro z
        have hsum : Tendsto (fun i => innerSL ℝ z (A i (x + y))) l
            (𝓝 (innerSL ℝ z (f x + f y))) := by
          simpa only [map_add] using (hweak x (innerSL ℝ z)).add (hweak y (innerSL ℝ z))
        exact tendsto_nhds_unique (hweak (x + y) (innerSL ℝ z)) hsum
      map_smul' := by
        intro r x
        apply ext_inner_left ℝ
        intro z
        have hmul : Tendsto (fun i => innerSL ℝ z (A i (r • x))) l
            (𝓝 (innerSL ℝ z (r • f x))) := by
          simpa only [map_smul, smul_eq_mul] using (hweak x (innerSL ℝ z)).const_mul r
        exact tendsto_nhds_unique (hweak (r • x) (innerSL ℝ z)) hmul }
  let B : E →L[ℝ] H := B₀.mkContinuous C hnorm
  exact ⟨B, fun _ => rfl, B.opNorm_le_bound hC hnorm⟩

/-- Theorem 3.1, regularity of Green limits: a common Lipschitz bound
passes through pointwise weak convergence on any subset of a metric domain.
The subset may be empty and the bound may be zero. -/
theorem lipschitzOnWith_of_weak_tendsto
    {X H : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {I : Type*} {l : Filter I} [NeBot l] (s : Set X)
    (u : I → X → H) (v : X → H) (K : ℝ≥0)
    (hweak : ∀ x ∈ s, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun i => ℓ (u i x)) l (𝓝 (ℓ (v x))))
    (hbound : ∀ᶠ i in l, LipschitzOnWith K (u i) s) :
    LipschitzOnWith K v s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm]
  apply norm_le_of_weak_tendsto (l := l) (fun i => u i x - u i y) (v x - v y)
  · intro ℓ
    simpa only [map_sub] using (hweak x hx ℓ).sub (hweak y hy ℓ)
  · filter_upwards [hbound] with i hi
    simpa only [dist_eq_norm] using hi.dist_le_mul x hx y hy


end KVApproximation.Analysis
