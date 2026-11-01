module

public import KVApproximation.Homogenization.SpatialEvolutionOperators
public import Mathlib.Analysis.Normed.Algebra.Spectrum

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicSpectrum.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

/-- Remark 1.2 (`rem:2`): positive spectral bounds for the actual
microscopic viscosity-inverse-elasticity operator can be chosen before
every nonzero scale. -/
theorem exists_uniform_microscopic_spectrum_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ (ε : ℝ) (hε : ε ≠ 0),
      spectrum ℝ (microscopicRelaxation V E hΩ ε hε) ⊆ Set.Icc a b := by
  sorry

end KVApproximation.Homogenization
