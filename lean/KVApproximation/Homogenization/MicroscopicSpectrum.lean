module

public import KVApproximation.Homogenization.SpatialEvolutionProperties
public import KVApproximation.OperatorTheory.RelativeRieszSpectrum

/-!
# Uniform microscopic relaxation rates
-/

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory

namespace KVApproximation.Homogenization

/-- Remark 1.2, uniform form bounds: choose the common spectral interval
before the admissible index in the underlying Hilbert space. -/
private theorem spectrum_bounds_of_uniform_form_bounds
    {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : I → Prop) (V E : (i : I) → P i → CoerciveForm H)
    (hV : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ i hi, (V i hi).HasBounds α β)
    (hE : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ i hi, (E i hi).HasBounds α β) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ i hi,
      spectrum ℝ (relativeRiesz (V i hi) (E i hi)) ⊆ Set.Icc a b := by
  obtain ⟨αV, βV, hαV, hβV, hV⟩ := hV
  obtain ⟨αE, βE, hαE, hβE, hE⟩ := hE
  refine ⟨αE / βV, βE / αV, div_pos hαE hβV, div_pos hβE hαV, ?_⟩
  intro i hi
  exact relativeRiesz_spectrum_subset (V i hi) (E i hi)
    hαV hβV hαE hβE (hV i hi) (hE i hi)

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
  exact spectrum_bounds_of_uniform_form_bounds (H := ZeroBoundaryH1 Ω)
    (fun ε : ℝ => ε ≠ 0)
    (fun ε hε => periodicSpatialForm V hΩ ε hε)
    (fun ε hε => periodicSpatialForm E hΩ ε hε)
    (exists_uniform_periodicSpatialForm_bounds V hΩ)
    (exists_uniform_periodicSpatialForm_bounds E hΩ)

end KVApproximation.Homogenization
