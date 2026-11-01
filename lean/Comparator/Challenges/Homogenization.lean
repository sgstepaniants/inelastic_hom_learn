module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Homogenization.WeakProblem

/-!
# Continuum periodic homogenization
-/

public section

open Filter TopologicalSpace
open scoped Topology InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`): the actual periodic
cell forms define the effective tensors and memory kernel. The unique
microscopic solutions converge weakly in `H¹(0,T;H¹₀(Ω;ℝᵈ))` along the whole
positive-scale family. Weak convergence is tested against every continuous
linear functional on that Sobolev space. -/
theorem viscoelastic_homogenization {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
    (Ω : Opens (PhysicalSpace d))
    (hΩbounded : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (hΩlipschitz : HasLipschitzBoundary (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (V E : CoerciveField d)
    (g₀ : SpatialL2 Ω) (u₀ : ℝ → ZeroBoundaryH1 Ω)
    (hprepared : IsPreparedInitialFamily E g₀ u₀) (f : Forcing Ω T) :
    ∃ C : CellConstitutiveModel V E,
      PositiveDefinite C.viscosity ∧ PositiveDefinite C.elasticity ∧
      Continuous C.kernel ∧
      (∀ t : ℝ, 0 ≤ t → ∀ e : Symmetric d,
        0 ≤ ⟪e, action (C.kernel t) e⟫_ℝ) ∧
      ∃ (u : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T)
        (uHom : TimeH1 (ZeroBoundaryH1 Ω) T),
        (∀ ε : ℝ, 0 < ε →
          IsMicroscopicSolution hT V E ε (u₀ ε) f (u ε) ∧
          ∀ v : TimeH1 (ZeroBoundaryH1 Ω) T,
            IsMicroscopicSolution hT V E ε (u₀ ε) f v → v = u ε) ∧
        IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f uHom ∧
        (∀ v : TimeH1 (ZeroBoundaryH1 Ω) T,
          IsHomogenizedSolution hT C.viscosity C.elasticity C.kernel g₀ f v → v = uHom) ∧
        ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
          Tendsto (fun ε => ℓ (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ uHom)) := by
  sorry

end KVApproximation.Homogenization
