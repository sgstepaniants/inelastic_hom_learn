module

public import KVApproximation.Analysis.TimeSobolevCompactness
public import KVApproximation.Analysis.HilbertWeakDiagonal
public import KVApproximation.Analysis.HilbertWeakLimits
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Compatible weak limits on the nonnegative time axis
-/

public section

noncomputable section

open Filter
open scoped Topology NNReal InnerProductSpace

namespace KVApproximation.Analysis

attribute [local instance] TimeSobolevCompactness.instInnerProductSpace

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
  obtain ⟨wLim, hLim, φ, hφ, hweak⟩ :=
    exists_weakly_convergent_diagonal_subsequence w C hw
  have hTk (k : ℕ) : 0 < T + k := add_pos_of_pos_of_nonneg hT (Nat.cast_nonneg k)
  have htraceWeak (k : ℕ) (t : Set.Icc (0 : ℝ) (T + k)) (ℓ : H →L[ℝ] ℝ) :
      Tendsto (fun n => ℓ (u (φ n) ⟨t, t.property.1⟩)) atTop
        (𝓝 (ℓ (TimeH1.trace (hTk k) (wLim k) t))) := by
    simpa only [htrace] using TimeH1.weak_trace_tendsto (hTk k)
      (fun n => w k (φ n)) (wLim k) (hweak k) t ℓ
  have hcover (t : Set.Ici (0 : ℝ)) : (t : ℝ) ≤ T + (⌈(t : ℝ)⌉₊ : ℝ) :=
    (Nat.le_ceil (t : ℝ)).trans (le_add_of_nonneg_left hT.le)
  let v (t : Set.Ici (0 : ℝ)) : H :=
    TimeH1.trace (hTk ⌈(t : ℝ)⌉₊) (wLim ⌈(t : ℝ)⌉₊) ⟨t, t.property, hcover t⟩
  have hpoint (t : Set.Ici (0 : ℝ)) (ℓ : H →L[ℝ] ℝ) :
      Tendsto (fun n => ℓ (u (φ n) t)) atTop (𝓝 (ℓ (v t))) :=
    htraceWeak ⌈(t : ℝ)⌉₊ ⟨t, t.property, hcover t⟩ ℓ
  have hnorm (t : Set.Ici (0 : ℝ)) : ‖v t‖ ≤ M :=
    norm_le_of_weak_tendsto (fun n => u (φ n) t) (v t) (hpoint t)
      (Eventually.of_forall (fun n => hvalue (φ n) t))
  have hvLip : LipschitzWith K v := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [dist_eq_norm]
    apply norm_le_of_weak_tendsto (l := atTop)
      (fun n => u (φ n) s - u (φ n) t) (v s - v t)
    · intro ℓ
      simpa only [map_sub] using (hpoint s ℓ).sub (hpoint t ℓ)
    · exact Eventually.of_forall (fun n => by
        simpa only [dist_eq_norm] using (hlip (φ n)).dist_le_mul s t)
  refine ⟨φ, hφ, wLim, hLim, hweak, ⟨v, hvLip.continuous⟩, hvLip, hnorm, ?_, hpoint⟩
  intro k t
  apply ext_inner_left ℝ
  intro z
  exact tendsto_nhds_unique (htraceWeak k t (innerSL ℝ z))
    (hpoint ⟨t, t.property.1⟩ (innerSL ℝ z))

end KVApproximation.Analysis
