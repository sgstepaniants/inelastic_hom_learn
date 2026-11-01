module

public import KVApproximation.Homogenization.MicroscopicTrajectory
public import KVApproximation.Homogenization.StaticCellOperators
public import KVApproximation.Tensor.FieldCombinations
public import KVApproximation.Analysis.HalfLineLaplace

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogenizedLaplace.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedLaplace.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

/-- Theorem 3.1, elastic preparation in the Laplace-domain limit:
the transformed velocity solves the effective combined-coefficient
equation with load -g/s. -/
theorem prepared_laplace_equilibrium (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hpos : ∀ n, 0 < ε n) (q : ℕ → ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ n, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic E.field (ε n)) (q n) v = loadPairing g v)
    (qLim L : ZeroBoundaryH1 Ω) {s : ℝ} (hs : 0 < s)
    (hqWeak : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (q n)) atTop (𝓝 (ℓ qLim)))
    (hLap : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (halfLineLaplace (F := ZeroBoundaryH1 Ω)
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s))
        atTop (𝓝 (ℓ L))) :
    ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le))
          (symmetricGradient (s • L - qLim) x) (symmetricGradient v x)) =
            -s⁻¹ * loadPairing g v := by
  sorry

/-- Theorem 3.1, viscous preparation in the Duhamel argument:
the displacement transform solves the effective combined-coefficient
equation with load g/s. -/
theorem viscous_laplace_equilibrium (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (hpos : ∀ n, 0 < ε n) (q : ℕ → ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ n, ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic V.field (ε n)) (q n) v = loadPairing g v)
    (L : ZeroBoundaryH1 Ω) {s : ℝ} (hs : 0 < s)
    (hLap : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (halfLineLaplace (F := ZeroBoundaryH1 Ω)
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hpos n).ne' (q n)) s))
        atTop (𝓝 (ℓ L))) :
    ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)),
        effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le))
          (symmetricGradient L x) (symmetricGradient v x)) =
            s⁻¹ * loadPairing g v := by
  sorry

end KVApproximation.Homogenization
