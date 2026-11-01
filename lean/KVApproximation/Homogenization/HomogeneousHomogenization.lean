module

public import KVApproximation.Homogenization.HomogeneousConvergence
public import KVApproximation.Homogenization.MicroscopicSolutionFamily

/-!
# Existence and uniqueness with zero forcing
-/

public section

noncomputable section

open TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, existence from convergence: select prepared data and
microscopic solutions, then retain the limiting solution and its uniqueness. -/
private theorem exists_unique_of_family_limit {Q X Y : Type*}
    {P B : Q → Prop} {M : Q → X → Prop} {S : Y → Prop} {W : X → Y → Prop}
    (hprepared : ∃ q, P q ∧ B q)
    (hfamily : ∀ q, ∃ u, M q u)
    (hlimit : ∀ q, P q → ∀ u, M q u →
      ∃ v, S v ∧ (∀ w, S w → w = v) ∧ W u v) : ∃! v, S v := by
  obtain ⟨q, hq, _⟩ := hprepared
  obtain ⟨u, hu⟩ := hfamily q
  obtain ⟨v, hv, huniq, _⟩ := hlimit q hq u hu
  exact ⟨v, hv, huniq⟩

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), zero forcing:
every L² initial load has a unique finite-horizon homogenized weak solution
with the actual cell tensors and memory kernel. -/
theorem homogeneous_exists_unique
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (g₀ : SpatialL2 Ω) :
    ∃! u : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsHomogenizedSolution (Ω := Ω) (T := T) hT C.viscosity C.elasticity C.kernel g₀ 0 u := by
  exact exists_unique_of_family_limit
    (P := fun (q : ℝ → ZeroBoundaryH1 Ω) => IsPreparedInitialFamily (Ω := Ω) E g₀ q)
    (M := fun q (u : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T) =>
      ∀ ε : ℝ, 0 < ε → IsMicroscopicSolution (Ω := Ω) (T := T) hT V E ε (q ε) 0 (u ε))
    (S := fun (w : TimeH1 (ZeroBoundaryH1 Ω) T) =>
      IsHomogenizedSolution (Ω := Ω) (T := T) hT
        C.viscosity C.elasticity C.kernel g₀ 0 w)
    (@exists_preparedInitialFamily d Ω E hΩ g₀)
    (fun q => @exists_microscopic_solution_family d Ω V E hΩ T hT q 0)
    (fun q hq u hu => @homogeneous_homogenization d Ω V E C hΩ T hT g₀ q hq u hu)

end KVApproximation.Homogenization
