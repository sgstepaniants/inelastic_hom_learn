module

public import KVApproximation.Homogenization.SpatialEvolutionOperators
public import KVApproximation.Homogenization.WeakProblem
public import Mathlib.Analysis.SpecialFunctions.Exponential

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicEvolution.instNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) :=
  { (inferInstance : SeminormedAddCommGroup (ZeroBoundaryH1 Ω)) with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

local instance MicroscopicEvolution.instNormable : IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

local instance MicroscopicEvolution.instTopologicalRing : IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ) (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1 (`eq:two_scale_weak_form`): the actual microscopic
weak PDE is equivalent to the spatial Hilbert-valued evolution equation,
including its initial trace and common exceptional time set. -/
theorem microscopic_solution_iff_ode (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    (q₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T) :
    IsMicroscopicSolution hT V E ε q₀ f u ↔
      TimeH1.initial (H := ZeroBoundaryH1 Ω) hT u = q₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity (H := ZeroBoundaryH1 Ω) u t =
            -microscopicRelaxation V E hΩ ε hε.ne'
              (TimeH1.value (H := ZeroBoundaryH1 Ω) u t) +
              microscopicLoadL V hΩ ε hε.ne' (f t) := by
  sorry

/-- Theorem 3.1, microscopic well-posedness: every positive scale,
Dirichlet initial value and L² forcing give a unique actual weak solution. -/
theorem microscopic_exists_unique (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    (q₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T) :
    ∃! u : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsMicroscopicSolution hT V E ε q₀ f u := by
  sorry

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, microscopic Duhamel formula: the actual solution trace
is the homogeneous evolution of its initial value plus viscously prepared forcing. -/
theorem microscopic_duhamel (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    (q₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsMicroscopicSolution hT V E ε q₀ f u) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace (H := ZeroBoundaryH1 Ω) hT u t =
      (NormedSpace.exp (-(t : ℝ) • microscopicRelaxation V E hΩ ε hε.ne')) q₀ +
        ∫ s in (0 : ℝ)..(t : ℝ),
          (NormedSpace.exp (-((t : ℝ) - s) • microscopicRelaxation V E hΩ ε hε.ne'))
            (microscopicLoadL V hΩ ε hε.ne' (f s)) := by
  sorry

end KVApproximation.Homogenization
