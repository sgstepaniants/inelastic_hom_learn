module

public import KVApproximation.Homogenization.MicroscopicTrajectory
public import KVApproximation.Homogenization.WeakProblem
public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.Topology.MetricSpace.Lipschitz

public section

noncomputable section

open Filter TopologicalSpace
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicCompactness.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

/-- Theorem 3.1, homogeneous compactness: uniformly bounded initial states
give one subsequence of the actual microscopic evolutions converging weakly
in the prescribed finite-time H¹ space, at every nonnegative time, and in
every positive-rate Laplace transform. The limit traces agree at both endpoints.
Elastic and viscous preparation can each supply the initial bound. -/
theorem microscopic_homogeneous_subsequence (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) {T : ℝ} (hT : 0 < T)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (q : ℕ → ZeroBoundaryH1 Ω)
    {B : ℝ} (hq : ∀ n, ‖q n‖ ≤ B)
    (u : ℕ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ n, IsMicroscopicSolution hT V E (ε n) (q n) 0 (u n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T, ∃ v : ℝ → ZeroBoundaryH1 Ω,
        ContinuousOn v (Set.Ici (0 : ℝ)) ∧
        (∃ M : ℝ, 0 ≤ M ∧ (∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M) ∧
          LipschitzOnWith (Real.toNNReal M) v (Set.Ici (0 : ℝ))) ∧
        (∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace (H := ZeroBoundaryH1 Ω) hT uLim t = v t) ∧
        (∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim))) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (microscopicTrajectory V E hΩ
            (ε (φ n)) (hε (φ n)).ne' (q (φ n)) t)) atTop (𝓝 (ℓ (v t)))) ∧
        ∀ s : ℝ, 0 < s → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (halfLineLaplace (F := ZeroBoundaryH1 Ω) (microscopicTrajectory V E hΩ
            (ε (φ n)) (hε (φ n)).ne' (q (φ n))) s)) atTop
            (𝓝 (ℓ (halfLineLaplace (F := ZeroBoundaryH1 Ω) v s))) := by
  sorry

end KVApproximation.Homogenization
