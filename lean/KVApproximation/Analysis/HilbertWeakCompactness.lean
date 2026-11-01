module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weak subsequences in Hilbert space

Sequential Banach–Alaoglu and Riesz representation give weak compactness
in the separable closed span of a sequence. Restricting ambient functionals
to that span removes any separability assumption on the original space.
-/

public section

noncomputable section

open Filter TopologicalSpace
open scoped Topology InnerProductSpace

namespace KVApproximation.Analysis

private theorem weak_subsequence_separable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SeparableSpace H] (u : ℕ → H) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ uLim : H, ‖uLim‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ℓ : H →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  let w (n : ℕ) : WeakDual ℝ H :=
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
  have hw (n : ℕ) : w n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) C := by
    change InnerProductSpace.toDual ℝ H (u n) ∈ Metric.closedBall 0 C
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨z, hz, φ, hφ, hconv⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) C hw
  let v := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual z)
  have hv : ‖v‖ ≤ C := by
    change WeakDual.toStrongDual z ∈ Metric.closedBall 0 C at hz
    simpa only [v, LinearIsometryEquiv.norm_map, Metric.mem_closedBall, dist_zero_right] using hz
  refine ⟨v, hv, φ, hφ, ?_⟩
  intro ℓ
  let y := (InnerProductSpace.toDual ℝ H).symm ℓ
  have hpair (x : H) : InnerProductSpace.toDual ℝ H x y = ℓ x := by
    rw [InnerProductSpace.toDual_apply_apply, real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hzpair : z y = ℓ v := by
    change WeakDual.toStrongDual z y = ℓ v
    rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have heval := (WeakDual.eval_continuous y).tendsto z |>.comp hconv
  change Tendsto (fun n => InnerProductSpace.toDual ℝ H (u (φ n)) y) atTop (𝓝 (z y)) at heval
  simpa only [hpair, hzpair] using heval

/-- Theorem 3.1, static homogenization: a bounded sequence in a complete
real Hilbert space has a weakly convergent subsequence with the same norm bound.
No separability assumption on the ambient space is needed. -/
theorem exists_weakly_convergent_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ uLim : H, ‖uLim‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ℓ : H →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  let S := (Submodule.span ℝ (Set.range u)).topologicalClosure
  have hsep : IsSeparable (S : Set H) := (Set.countable_range u).isSeparable.span.closure
  let : SeparableSpace S := hsep.separableSpace
  let v (n : ℕ) : S :=
    ⟨u n, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)⟩
  obtain ⟨vLim, hvLim, φ, hφ, hweak⟩ := weak_subsequence_separable v hu
  refine ⟨vLim, hvLim, φ, hφ, ?_⟩
  intro ℓ
  exact hweak (ℓ.comp S.subtypeL)

end KVApproximation.Analysis
