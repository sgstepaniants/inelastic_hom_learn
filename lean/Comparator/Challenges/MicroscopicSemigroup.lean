module

public import KVApproximation.Homogenization.SpatialEvolutionOperators
public import Mathlib.Analysis.SpecialFunctions.Exponential

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicSemigroup.instNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance MicroscopicSemigroup.instNormable : IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

local instance MicroscopicSemigroup.instTopologicalRing : IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ) (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1, homogeneous microscopic evolution: the actual spatial
semigroup has its prescribed Hilbert-valued derivative. -/
theorem microscopic_homogeneous_hasDerivAt (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (NormedSpace.exp (-s • microscopicRelaxation V E hΩ ε hε)) q)
      (-microscopicRelaxation V E hΩ ε hε
        ((NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q)) t := by
  sorry

/-- Theorem 3.1, uniform half-line estimate: one constant bounds the
actual homogeneous spatial trajectory and its velocity at every nonnegative
time, before choosing the microscopic scale or initial displacement. -/
theorem exists_uniform_microscopic_semigroup_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω)
      (t : ℝ), 0 ≤ t →
      ‖(NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q‖ ≤ C * ‖q‖ ∧
      ‖-microscopicRelaxation V E hΩ ε hε
        ((NormedSpace.exp (-t • microscopicRelaxation V E hΩ ε hε)) q)‖ ≤ C * ‖q‖ := by
  sorry

end KVApproximation.Homogenization
