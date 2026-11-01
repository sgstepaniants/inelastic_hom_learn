module

public import KVApproximation.Analysis.HilbertWeakCompactness

/-!
# Simultaneous weak subsequences in countably many Hilbert spaces
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, diagonal extraction: a sequence eventually lying in a
convergent subsequence's range has the same limit if its indices tend to infinity. -/
private theorem tendsto_of_eventually_mem_range
    {X : Type*} {l : Filter X} (y : ℕ → X) (f ψ : ℕ → ℕ)
    (hf : StrictMono f) (hψ : Tendsto ψ atTop atTop)
    (hrange : ∀ᶠ n in atTop, ψ n ∈ Set.range f)
    (hlim : Tendsto (fun n => y (f n)) atTop l) :
    Tendsto (fun n => y (ψ n)) atTop l := by
  apply tendsto_iff_eventually.mpr
  intro p hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually hp)
  filter_upwards [hrange, hψ.eventually (eventually_ge_atTop (f N))] with n hn hlarge
  obtain ⟨j, hj⟩ := hn
  rw [← hj] at hlarge ⊢
  exact hN j (hf.le_iff_le.mp hlarge)

/-- Theorem 3.1, half-line compactness: one strictly increasing subsequence
converges weakly in every member of a countable family of complete Hilbert spaces,
retaining the individual norm bounds and requiring no ambient separability. -/
theorem exists_weakly_convergent_diagonal_subsequence
    {H : ℕ → Type*} [∀ k, NormedAddCommGroup (H k)]
    [∀ k, InnerProductSpace ℝ (H k)] [∀ k, CompleteSpace (H k)]
    (u : ∀ k, ℕ → H k) (C : ℕ → ℝ) (hu : ∀ k n, ‖u k n‖ ≤ C k) :
    ∃ uLim : ∀ k, H k, (∀ k, ‖uLim k‖ ≤ C k) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k (ℓ : H k →L[ℝ] ℝ),
        Tendsto (fun n => ℓ (u k (φ n))) atTop (𝓝 (ℓ (uLim k))) := by
  have hsub (k : ℕ) (r : ℕ → ℕ) :
      ∃ v : H k, ‖v‖ ≤ C k ∧ ∃ g : ℕ → ℕ, StrictMono g ∧
        ∀ ℓ : H k →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (u k (r (g n)))) atTop (𝓝 (ℓ v)) :=
    exists_weakly_convergent_subsequence (fun n => u k (r n)) (fun n => hu k (r n))
  choose v hv g hg hconv using hsub
  let f : ℕ → ℕ → ℕ := Nat.rec (fun n => n) (fun k r n => r (g k r n))
  have hf (k : ℕ) : StrictMono (f k) := by
    induction k with
    | zero => exact strictMono_id
    | succ k ih => exact ih.comp (hg k (f k))
  have hrange {a b : ℕ} (hab : a ≤ b) : Set.range (f b) ⊆ Set.range (f a) := by
    induction b, hab using Nat.le_induction with
    | base => exact Set.Subset.rfl
    | succ b hab ih =>
      rintro x ⟨n, rfl⟩
      exact ih ⟨g b (f b) n, rfl⟩
  let φ (n : ℕ) := f (n + 1) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change f (n + 1) n < f (n + 1) (g (n + 1) (f (n + 1)) (n + 1))
    exact (hf (n + 1) (Nat.lt_succ_self n)).trans_le
      ((hf (n + 1)).monotone ((hg (n + 1) (f (n + 1))).id_le (n + 1)))
  refine ⟨fun k => v k (f k), fun k => hv k (f k), φ, hφ, ?_⟩
  intro k ℓ
  apply tendsto_of_eventually_mem_range (fun n => ℓ (u k n)) (f (k + 1)) φ
    (hf (k + 1)) hφ.tendsto_atTop
  · filter_upwards [eventually_ge_atTop k] with n hn
    exact hrange (Nat.add_le_add_right hn 1) ⟨n, rfl⟩
  · exact hconv k (f k) ℓ

end KVApproximation.Analysis
