module

public import KVApproximation.Homogenization.MicroscopicEvolution

/-!
# Families of microscopic solutions
-/

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, family selection: ordinary choice extends solutions
from a nonempty set of indices, without any regularity in the index. -/
private theorem exists_guarded_family {I X : Type*}
    (S : I → Prop) (P : I → X → Prop) (i₀ : I) (hi₀ : S i₀)
    (h : ∀ i, S i → ∃! x, P i x) :
    ∃ u : I → X, ∀ i, S i → P i (u i) := by
  classical
  let x₀ : X := (h i₀ hi₀).choose
  have hex (i : I) : ∃ x : X, S i → P i x := by
    by_cases hi : S i
    · obtain ⟨x, hx, _⟩ := h i hi
      exact ⟨x, fun _ => hx⟩
    · exact ⟨x₀, fun hsi => False.elim (hi hsi)⟩
  exact ⟨fun i => (hex i).choose, fun i => (hex i).choose_spec⟩

/-- Theorem 3.1, selection of microscopic solutions: prescribed initial
data and forcing admit a family solving the actual PDE at every positive scale. -/
theorem exists_microscopic_solution_family
    {d : ℕ} {Ω : Opens (PhysicalSpace d)} (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (q : ℝ → ZeroBoundaryH1 Ω) (f : Forcing Ω T) :
    ∃ u : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T,
      ∀ ε : ℝ, 0 < ε →
        IsMicroscopicSolution (Ω := Ω) (T := T) hT V E ε (q ε) f (u ε) := by
  exact exists_guarded_family (X := TimeH1 (ZeroBoundaryH1 Ω) T)
    (fun ε : ℝ => 0 < ε)
    (fun ε z => IsMicroscopicSolution (Ω := Ω) (T := T) hT V E ε (q ε) f z)
    1 zero_lt_one
    (fun ε hε => @microscopic_exists_unique d Ω V E hΩ ε hε T hT (q ε) f)

end KVApproximation.Homogenization
