module

public import KVApproximation.Homogenization.CorrectorRange
public import KVApproximation.Analysis.PeriodicMeanRemoval

/-!
# Periodic displacement and strain-corrector tests
-/

public section

open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Appendix A.3, testing in `eq:cell_weak`: all periodic displacement
tests are equivalent to all strain-corrector tests. -/
theorem periodic_test_iff_corrector_test {d : ℕ} (σ : StrainField d) :
    (∀ φ : PeriodicH1 d, ⟪σ, PeriodicH1.symmetricGradientL d φ⟫_ℝ = 0) ↔
      ∀ ψ : (correctorSubspace d).toSubmodule, ⟪σ, (ψ : StrainField d)⟫_ℝ = 0 := by
  constructor
  · intro h ψ
    have hmem : (ψ : StrainField d) ∈ (correctorGradientL d).range := by
      simpa only [correctorSubspace_eq_range] using ψ.property
    obtain ⟨φ, hφ⟩ := hmem
    rw [← hφ]
    exact h (φ : PeriodicH1 d)
  · intro h φ
    obtain ⟨v, _, hgrad⟩ := PeriodicH1.exists_zeroMean_same_gradient φ
    have hs : correctorGradientL d v = PeriodicH1.symmetricGradientL d φ :=
      congrArg ((symmetrizeL d).compLpL 2 (cellMeasure d)) hgrad
    have hv : correctorGradientL d v ∈ (correctorSubspace d).toSubmodule := by
      rw [correctorSubspace_eq_range]
      exact ⟨v, rfl⟩
    have ht := h ⟨correctorGradientL d v, hv⟩
    change ⟪σ, correctorGradientL d v⟫_ℝ = 0 at ht
    rwa [hs] at ht

end KVApproximation.Homogenization
