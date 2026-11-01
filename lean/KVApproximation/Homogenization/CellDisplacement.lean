module

public import KVApproximation.Homogenization.CorrectorTrajectory
public import KVApproximation.Homogenization.CellOperators

/-!
# The periodic displacement cell problem
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Section 3.1 (`eq:cell_stress`): the L² stress obtained by applying the
actual periodic viscosity and elasticity fields to the total strain rate
and strain. -/
def periodicCellStress {d : ℕ} (V E : CoerciveField d) {T : ℝ}
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (t : ℝ) : StrainField d :=
  multiplication V.field
      (constantStrainL d (TimeH1.velocity (H := Symmetric d) (T := T) e t) +
        correctorGradientL d (TimeH1.velocity (H := ZeroMeanPeriodicH1 d) (T := T) χ t)) +
    multiplication E.field
      (constantStrainL d (TimeH1.value (H := Symmetric d) (T := T) e t) +
        correctorGradientL d (TimeH1.value (H := ZeroMeanPeriodicH1 d) (T := T) χ t))

/-- Section 3.1 (`eqns:cell_problem`) and Appendix A.3: weak periodic
force balance and the static elastic preparation of the initial displacement.
The zero-mean condition is part of the displacement space. The exceptional
time-null set is chosen before the periodic test displacement. -/
def IsPeriodicCellSolution {d : ℕ} (V E : CoerciveField d) {T : ℝ} (hT : 0 < T)
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T) : Prop :=
  (∀ φ : PeriodicH1 d,
    ⟪multiplication E.field
      (constantStrainL d (TimeH1.initial (H := Symmetric d) (T := T) hT e) +
        correctorGradientL d (TimeH1.initial (H := ZeroMeanPeriodicH1 d) (T := T) hT χ)),
      PeriodicH1.symmetricGradientL d φ⟫_ℝ = 0) ∧
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ φ : PeriodicH1 d,
      ⟪periodicCellStress (d := d) (T := T) V E e χ t,
        PeriodicH1.symmetricGradientL d φ⟫_ℝ = 0

/-- Section 3.1 and Appendix A.3 (`eq:stress_decomp`): the macroscopic
stress is the spatial Bochner integral of the actual cell stress over the
normalized periodic cell. -/
def averagedCellStress {d : ℕ} (V E : CoerciveField d) {T : ℝ}
    (e : TimeH1 (Symmetric d) T) (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (t : ℝ) : Symmetric d :=
  ∫ y, periodicCellStress (d := d) (T := T) V E e χ t y ∂cellMeasure d

end KVApproximation.Homogenization
