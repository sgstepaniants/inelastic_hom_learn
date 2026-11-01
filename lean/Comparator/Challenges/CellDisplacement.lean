module

public import KVApproximation.Homogenization.CellDisplacement
public import KVApproximation.Dynamics.CellEvolution

/-!
# Periodic displacement balance and averaged stress
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Dynamics

namespace KVApproximation.Homogenization

/-- Appendix A.3, testing in `eq:cell_weak`: all periodic displacement
tests are equivalent to all strain-corrector tests. -/
theorem periodic_test_iff_corrector_test {d : ℕ} (σ : StrainField d) :
    (∀ φ : PeriodicH1 d, ⟪σ, PeriodicH1.symmetricGradientL d φ⟫_ℝ = 0) ↔
      ∀ ψ : (correctorSubspace d).toSubmodule, ⟪σ, (ψ : StrainField d)⟫_ℝ = 0 := by
  sorry

/-- Section 3.1 (`eq:cell_stress`): the L² stress has the prescribed
pointwise constitutive representative for almost every cell position. -/
theorem periodicCellStress_apply_ae {d : ℕ} (V E : CoerciveField d) {T : ℝ}
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T) (t : ℝ) :
    periodicCellStress (d := d) (T := T) V E e χ t =ᵐ[cellMeasure d] fun y =>
      action (V.field y)
        (TimeH1.velocity (H := Symmetric d) (T := T) e t +
          correctorGradientL d (TimeH1.velocity (H := ZeroMeanPeriodicH1 d) (T := T) χ t) y) +
      action (E.field y)
        (TimeH1.value (H := Symmetric d) (T := T) e t +
          correctorGradientL d (TimeH1.value (H := ZeroMeanPeriodicH1 d) (T := T) χ t) y) := by
  sorry

/-- Appendix A.3 (`eq:cell_weak`): the actual displacement-valued periodic
PDE is equivalent to the tested strain-corrector evolution, including its
elasticity-prepared initial condition. -/
theorem periodicCellSolution_iff_evolution {d : ℕ} (V E : CoerciveField d)
    {T : ℝ} (hT : 0 < T) (e : TimeH1 (Symmetric d) T)
    (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (η : TimeH1 (correctorSubspace d) T)
    (h : IsDisplacementStrain (d := d) (T := T) χ η) :
    IsPeriodicCellSolution (d := d) (T := T) V E hT e χ ↔
      IsCellEvolution (H := StrainField d) (F := Symmetric d)
        V.toForm E.toForm (correctorSubspace d) (constantStrainL d) hT e η := by
  sorry

/-- Section 3.1 (`eqns:cell_problem`) and Appendix A.3: the prepared periodic
cell PDE has a unique zero-mean H¹ displacement trajectory for each H¹
macroscopic strain history on a finite positive interval. -/
theorem periodicCellSolution_exists_unique {d : ℕ} (V E : CoerciveField d)
    {T : ℝ} (hT : 0 < T) (e : TimeH1 (Symmetric d) T) :
    ∃! χ : TimeH1 (ZeroMeanPeriodicH1 d) T,
      IsPeriodicCellSolution (d := d) (T := T) V E hT e χ := by
  sorry

/-- Appendix A.3, the identity before `eq:stress_decomp`: the spatially
averaged physical stress has the same pairings as the tested cell stress. -/
theorem averagedCellStress_pairing {d : ℕ} (V E : CoerciveField d) {T : ℝ}
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (η : TimeH1 (correctorSubspace d) T)
    (h : IsDisplacementStrain (d := d) (T := T) χ η) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ a : Symmetric d,
      ⟪a, averagedCellStress (d := d) (T := T) V E e χ t⟫_ℝ =
        cellStressPairing (H := StrainField d) (F := Symmetric d)
          V.toForm E.toForm (correctorSubspace d) (constantStrainL d) e η t a := by
  sorry

/-- Appendix A.3 and Remark 3.2: eliminating the displacement cell solution
gives the exact positive-memory constitutive law for its actual spatially
averaged stress. -/
theorem periodicCellSolution_constitutive {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {T : ℝ} (hT : 0 < T)
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (hχ : IsPeriodicCellSolution (d := d) (T := T) V E hT e χ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      averagedCellStress (d := d) (T := T) V E e χ t =
        action C.viscosity (TimeH1.velocity (H := Symmetric d) (T := T) e t) +
          action C.elasticity (TimeH1.value (H := Symmetric d) (T := T) e t) +
            ∫ s in (0 : ℝ)..t,
              action (C.kernel (t - s)) (TimeH1.velocity (H := Symmetric d) (T := T) e s) := by
  sorry

end KVApproximation.Homogenization
