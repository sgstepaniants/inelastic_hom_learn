module

public import KVApproximation.Homogenization.WeakProblem

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, selection of microscopic solutions: prescribed initial
data and forcing admit a family solving the actual PDE at every positive scale. -/
theorem exists_microscopic_solution_family
    {d : ℕ} {Ω : Opens (PhysicalSpace d)} (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (q : ℝ → ZeroBoundaryH1 Ω) (f : Forcing Ω T) :
    ∃ u : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T,
      ∀ ε : ℝ, 0 < ε →
        IsMicroscopicSolution (Ω := Ω) (T := T) hT V E ε (q ε) f (u ε) := by
  sorry

end KVApproximation.Homogenization
