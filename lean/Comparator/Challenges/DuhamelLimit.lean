module

public import KVApproximation.Homogenization.MicroscopicGreen
public import KVApproximation.Homogenization.WeakProblem

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel limit:
subtracting the microscopic homogeneous solution with the same initial data
leaves a forcing contribution whose traces converge weakly to the Green
convolution. The prescribed L² forcing needs no time continuity. -/
theorem microscopic_forcing_trace_tendsto
    (V E : CoerciveField d) (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (f : Forcing Ω T)
    (q : ℝ → ZeroBoundaryH1 Ω) (u v : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ ε : ℝ, 0 < ε → IsMicroscopicSolution hT V E ε (q ε) f (u ε))
    (hv : ∀ ε : ℝ, 0 < ε → IsMicroscopicSolution hT V E ε (q ε) 0 (v ε))
    (G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω) (hG : Continuous G)
    (hweak : ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
      ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (microscopicGreen (Ω := Ω) V E hΩ ε t g))
          (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (G t g)))) :
    ∀ t : Set.Icc (0 : ℝ) T, ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun ε => ℓ (TimeH1.trace hT (u ε) t - TimeH1.trace hT (v ε) t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (ℓ (∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)))) := by
  sorry

end KVApproximation.Homogenization
