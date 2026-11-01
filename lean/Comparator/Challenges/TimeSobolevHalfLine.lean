module

public import KVApproximation.Analysis.TimeSobolev
public import Mathlib.Topology.MetricSpace.Lipschitz

public section

open Filter
open scoped Topology NNReal

namespace KVApproximation.Analysis

/-- Theorem 3.1, half-line compactness: uniformly bounded Lipschitz
trajectories with bounded H¹ realizations on the horizons `T + k` have one
subsequence whose weak H¹ limits are the compatible traces of a single
bounded Lipschitz trajectory. The horizon `k = 0` is the prescribed interval. -/
theorem TimeH1.exists_halfLine_weak_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : ℝ} (hT : 0 < T) (u : ℕ → Set.Ici (0 : ℝ) → H)
    (w : ∀ k : ℕ, ℕ → TimeH1 H (T + k)) (C : ℕ → ℝ) {M : ℝ} {K : ℝ≥0}
    (hw : ∀ k n, ‖w k n‖ ≤ C k)
    (hvalue : ∀ n t, ‖u n t‖ ≤ M) (hlip : ∀ n, LipschitzWith K (u n))
    (htrace : ∀ (k n : ℕ) (t : Set.Icc (0 : ℝ) (T + k)),
      TimeH1.trace (add_pos_of_pos_of_nonneg hT (Nat.cast_nonneg k)) (w k n) t =
        u n ⟨t, t.property.1⟩) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ wLim : ∀ k : ℕ, TimeH1 H (T + k),
      (∀ k, ‖wLim k‖ ≤ C k) ∧
      (∀ (k : ℕ) (ℓ : TimeH1 H (T + k) →L[ℝ] ℝ),
        Tendsto (fun n => ℓ (w k (φ n))) atTop (𝓝 (ℓ (wLim k)))) ∧
      ∃ uLim : C(Set.Ici (0 : ℝ), H), LipschitzWith K uLim ∧
        (∀ t, ‖uLim t‖ ≤ M) ∧
        (∀ (k : ℕ) (t : Set.Icc (0 : ℝ) (T + k)),
          TimeH1.trace (add_pos_of_pos_of_nonneg hT (Nat.cast_nonneg k)) (wLim k) t =
            uLim ⟨t, t.property.1⟩) ∧
        ∀ t (ℓ : H →L[ℝ] ℝ),
          Tendsto (fun n => ℓ (u (φ n) t)) atTop (𝓝 (ℓ (uLim t))) := by
  sorry

end KVApproximation.Analysis
