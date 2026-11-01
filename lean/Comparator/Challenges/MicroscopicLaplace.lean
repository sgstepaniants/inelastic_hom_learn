module

public import KVApproximation.Homogenization.MicroscopicTrajectory
public import KVApproximation.Analysis.HalfLineLaplace

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicLaplace.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance MicroscopicLaplace.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

/-- Theorem 3.1, Laplace-domain argument: the transform of the actual
homogeneous trajectory satisfies the spatial relaxation equation. -/
theorem microscopicTrajectory_laplace_equation (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω) {s : ℝ} (hs : 0 < s) :
    s • halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s - q =
      -microscopicRelaxation V E hΩ ε hε
        (halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s) := by
  sorry

/-- Theorem 3.1, elastic preparation: the transformed velocity has
combined viscosity/elasticity form and load -g/s. -/
theorem microscopic_prepared_laplace_form (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic E.field ε) q v = loadPairing g v)
    {s : ℝ} (hs : 0 < s) (v : ZeroBoundaryH1 Ω) :
    let L := halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s
    spatialForm (rescalePeriodic V.field ε) (s • L - q) v +
      s⁻¹ * spatialForm (rescalePeriodic E.field ε) (s • L - q) v =
      -s⁻¹ * loadPairing g v := by
  sorry

/-- Theorem 3.1, Duhamel forcing: viscous preparation gives the
combined transformed form with load g/s for the displacement transform. -/
theorem microscopic_viscous_laplace_form (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic V.field ε) q v = loadPairing g v)
    {s : ℝ} (hs : 0 < s) (v : ZeroBoundaryH1 Ω) :
    let L := halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s
    spatialForm (rescalePeriodic V.field ε) L v +
      s⁻¹ * spatialForm (rescalePeriodic E.field ε) L v =
      s⁻¹ * loadPairing g v := by
  sorry

end KVApproximation.Homogenization
