module

public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# The periodic unit cell
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Section 2.1 (`subsec:formal_homogenization_settings`): the unit torus. -/
abbrev PeriodicCell (d : ℕ) := UnitAddTorus (Fin d)

/-- Section 2.1: normalized Lebesgue measure on the periodic unit cell.
The normalization is explicit and does not depend on a local volume instance. -/
def cellMeasure (d : ℕ) : Measure (PeriodicCell d) :=
  Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))

instance (d : ℕ) : IsProbabilityMeasure (cellMeasure d) := by
  unfold cellMeasure
  infer_instance

/-- Section 2.2 (`eqns:two_scale_problem`): passage from physical coordinates
to their classes modulo the integer lattice. -/
def toCell {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : PeriodicCell d :=
  fun i => (x i : UnitAddCircle)

/-- Sections 3.1 and 4.1: representatives in the product cell `(0,1]ᵈ`,
used to evaluate derivatives of periodic lifts. -/
def cellRepresentative {d : ℕ} (y : PeriodicCell d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (AddCircle.equivIoc 1 0 (y i)).val)

/-- Section 2.2: the periodic coefficient field sampled at scale `ε`. -/
def rescalePeriodic {d : ℕ} {F : Type*} (A : PeriodicCell d → F)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) : F :=
  A (toCell (ε⁻¹ • x))

end KVApproximation.Analysis
