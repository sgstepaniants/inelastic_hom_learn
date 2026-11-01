module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Homogenization.WeakProblem

public section

noncomputable section

open TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), zero forcing:
the whole family with elastically prepared initial data converges weakly
in H¹(0,T;H¹₀) to the unique weak solution with the actual cell tensors
and memory kernel. Bounded open spatial domains suffice. -/
theorem homogeneous_homogenization
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω)
    (q : ℝ → ZeroBoundaryH1 Ω) (hq : IsPreparedInitialFamily E g₀ q)
    (u : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ ε : ℝ, 0 < ε → IsMicroscopicSolution hT V E ε (q ε) 0 (u ε)) :
    ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ 0 uLim ∧
      (∀ w : TimeH1 (ZeroBoundaryH1 Ω) T,
        IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ 0 w → w = uLim) ∧
      ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ uLim)) := by
  sorry

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), zero forcing:
every L² initial load has a unique finite-horizon homogenized weak solution
with the actual cell tensors and memory kernel. -/
theorem homogeneous_exists_unique
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω) :
    ∃! u : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ 0 u := by
  sorry

end KVApproximation.Homogenization
