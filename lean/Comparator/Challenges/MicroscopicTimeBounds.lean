module

public import KVApproximation.Homogenization.WeakProblem

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicTimeBounds.instNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) :=
  inferInstance

local instance MicroscopicTimeBounds.instNormable : IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

/-- Theorem 3.1, finite-time compactness estimate: one positive constant
controls the actual microscopic H¹ trajectory before choosing its scale,
initial displacement or L² forcing. -/
theorem exists_uniform_microscopic_timeH1_bound (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε →
      ∀ (q₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T),
        IsMicroscopicSolution hT V E ε q₀ f u → ‖u‖ ≤ C * (‖q₀‖ + ‖f‖) := by
  sorry

/-- Theorem 3.1, admissible initial conditions: elastic preparation
gives a common finite-time H¹ bound in terms of the fixed initial load and
the time-dependent L² forcing. -/
theorem exists_uniform_prepared_timeH1_bound (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g₀ : SpatialL2 Ω) (u₀ : ℝ → ZeroBoundaryH1 Ω),
      IsPreparedInitialFamily E g₀ u₀ → ∀ (ε : ℝ), 0 < ε →
        ∀ (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T),
          IsMicroscopicSolution hT V E ε (u₀ ε) f u → ‖u‖ ≤ C * (‖g₀‖ + ‖f‖) := by
  sorry

end KVApproximation.Homogenization
