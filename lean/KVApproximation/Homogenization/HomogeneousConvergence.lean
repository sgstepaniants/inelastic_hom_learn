module

public import KVApproximation.Homogenization.HomogeneousSubsequence
public import KVApproximation.Homogenization.HomogenizedUniqueness
public import KVApproximation.Analysis.WeakSubsequenceLimit

/-!
# Homogenization with zero forcing

Prepared initial data give uniform microscopic bounds. Compactness and
Laplace-domain identification produce a homogenized solution, and uniqueness
identifies every subsequential limit of the whole positive-scale family.
-/

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
    (q : ℝ → ZeroBoundaryH1 Ω) (hq : IsPreparedInitialFamily (Ω := Ω) E g₀ q)
    (u : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ ε : ℝ, 0 < ε → IsMicroscopicSolution (Ω := Ω) (T := T) hT V E ε (q ε) 0 (u ε)) :
    ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution (Ω := Ω) (T := T) hT C.viscosity C.elasticity C.kernel g₀ 0 uLim ∧
      (∀ w : TimeH1 (ZeroBoundaryH1 Ω) T,
        IsHomogenizedSolution (Ω := Ω) (T := T) hT C.viscosity C.elasticity C.kernel g₀ 0 w → w = uLim) ∧
      ∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (u ε)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ uLim)) := by
  have hV : PositiveDefinite C.viscosity := by
    refine ⟨V.lower, V.lower_pos, fun e => ?_⟩
    rw [C.viscosity_eq]
    exact (effectiveForm_bounds V V.lower_pos V.bounds e).1
  have hE : PositiveDefinite C.elasticity := by
    refine ⟨E.lower, E.lower_pos, fun e => ?_⟩
    rw [C.elasticity_eq]
    exact (effectiveForm_bounds E E.lower_pos E.bounds e).1
  exact exists_test_limit_of_unique_subsequences
    (X := TimeH1 (ZeroBoundaryH1 Ω) T)
    (fun (ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ)
      (v : TimeH1 (ZeroBoundaryH1 Ω) T) => ℓ v)
    (fun w => IsHomogenizedSolution (Ω := Ω) (T := T) hT
      C.viscosity C.elasticity C.kernel g₀ 0 w) u
    (fun ε hε hpos => @prepared_homogeneous_subsequence d Ω V E C hΩ T hT g₀
      ε hε hpos (fun n => q (ε n)) (fun n => hq (ε n) (hpos n))
      (fun n => u (ε n)) (fun n => hu (ε n) (hpos n)))
    (fun v w hv hw => @homogenized_solution_unique d Ω hΩ T hT
      C.viscosity C.elasticity hV hE C.kernel (cellKernel_continuous V E C)
      g₀ 0 v w hv hw)

end KVApproximation.Homogenization
