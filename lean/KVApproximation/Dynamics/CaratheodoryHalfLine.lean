module

public import KVApproximation.Dynamics.Caratheodory

/-!
# Measurable-time integral equations on a half-line
-/

public section

open MeasureTheory Set
open scoped NNReal Topology

namespace KVApproximation.Dynamics

/-- Proposition B.13, global Carathéodory ingredient: compatible finite
interval solutions give a continuous integral solution on the half-line.
No uniform bound on its state is assumed or asserted here. -/
theorem exists_integral_solution_Ici {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} {a : ℝ} {K : ℝ≥0}
    (hLip : ∀ᵐ s ∂volume.restrict (Ici a), LipschitzWith K (f s))
    (hInt : ∀ b : ℝ, a ≤ b → ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b)) (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Ici a) ∧ x a = x₀ ∧
      ∀ t ∈ Ici a, x t = x₀ + ∫ s in a..t, f s (x s) := by
  classical
  have hLip' (b : ℝ) : ∀ᵐ s ∂volume.restrict (Icc a b), LipschitzWith K (f s) :=
    ae_restrict_of_ae_restrict_of_subset Icc_subset_Ici_self hLip
  have hex (b : Ici a) : ∃ x : ℝ → E, ContinuousOn x (Icc a b) ∧ x a = x₀ ∧
      ∀ t ∈ Icc a b, x t = x₀ + ∫ s in a..t, f s (x s) :=
    exists_integral_solution_Icc (hLip' b) (hInt b b.2) x₀
  choose X hX hX₀ hsol using hex
  have hcompat (b c : Ici a) (hbc : b ≤ c) : EqOn (X b) (X c) (Icc a b) :=
    integral_solution_unique_Icc (hLip' b) (hInt b b.2) (hX b)
      ((hX c).mono (Icc_subset_Icc_right hbc)) (hsol b)
      (fun t ht => hsol c t ⟨ht.1, ht.2.trans hbc⟩)
  let x : ℝ → E := fun t => if ht : a ≤ t then X ⟨t, ht⟩ t else x₀
  have heq (b : Ici a) : EqOn x (X b) (Icc a b) := by
    intro t ht
    dsimp only [x]
    rw [dite_eq_left ht.1]
    exact hcompat ⟨t, ht.1⟩ b ht.2 ⟨ht.1, le_rfl⟩
  have hc (b : Ici a) : ContinuousOn x (Icc a b) := (hX b).congr (heq b)
  refine ⟨x, ?_, ?_, ?_⟩
  · intro t ht
    have htb : t < t + 1 := by linarith
    have hab : a ≤ t + 1 := ht.trans htb.le
    have hlocal := hc ⟨t + 1, hab⟩ t ⟨ht, htb.le⟩
    apply hlocal.mono_of_mem_nhdsWithin
    exact Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds htb))
  · exact (heq ⟨a, le_rfl⟩ ⟨le_rfl, le_rfl⟩).trans (hX₀ ⟨a, le_rfl⟩)
  · intro t ht
    rw [heq ⟨t, ht⟩ ⟨ht, le_rfl⟩, hsol ⟨t, ht⟩ t ⟨ht, le_rfl⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    dsimp only
    rw [heq ⟨t, ht⟩ hs]

end KVApproximation.Dynamics
