module

public import KVApproximation.Homogenization.MicroscopicTrajectory
public import KVApproximation.Homogenization.WeakProblem
public import Mathlib.Topology.MetricSpace.Lipschitz

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicTrajectoryProperties.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance MicroscopicTrajectoryProperties.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

/-- Theorem 3.1, homogeneous compactness: the continuous trace of every
zero-forcing microscopic weak solution is the same global semigroup trajectory. -/
theorem microscopic_zero_forcing_trace (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    (q : ZeroBoundaryH1 Ω) (u : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsMicroscopicSolution hT V E ε q 0 u) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace (H := ZeroBoundaryH1 Ω) hT u t =
      microscopicTrajectory V E hΩ ε hε.ne' q t := by
  sorry

/-- Theorem 3.1, uniform half-line compactness: one constant chosen before
scale and initial data bounds the actual trajectory and its Lipschitz constant. -/
theorem exists_uniform_microscopicTrajectory_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω),
      (∀ t : ℝ, 0 ≤ t → ‖microscopicTrajectory V E hΩ ε hε q t‖ ≤ C * ‖q‖) ∧
      LipschitzOnWith (Real.toNNReal (C * ‖q‖))
        (microscopicTrajectory V E hΩ ε hε q) (Set.Ici (0 : ℝ)) := by
  sorry

end KVApproximation.Homogenization
