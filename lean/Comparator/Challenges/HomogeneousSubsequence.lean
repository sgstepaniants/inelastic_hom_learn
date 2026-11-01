module

public import KVApproximation.Homogenization.WeakProblem
public import KVApproximation.Homogenization.CellConstitutive

public section

noncomputable section

open TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, zero-forcing compactness: every positive approach sequence
has a weak time-Sobolev subsequence solving the actual cell-memory equation.
The initial weak limit is obtained by evaluating the weak trace at zero. -/
theorem prepared_homogeneous_subsequence
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) (hpos : ∀ n, 0 < ε n)
    (q : ℕ → ZeroBoundaryH1 Ω)
    (hq : ∀ n, ∀ w : ZeroBoundaryH1 Ω,
      spatialForm (Ω := Ω) (rescalePeriodic E.field (ε n)) (q n) w = loadPairing (Ω := Ω) g₀ w)
    (u : ℕ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ n, IsMicroscopicSolution (Ω := Ω) (T := T) hT V E (ε n) (q n) 0 (u n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution (Ω := Ω) (T := T) hT C.viscosity C.elasticity C.kernel g₀ 0 uLim ∧
      ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim)) := by
  sorry

end KVApproximation.Homogenization
