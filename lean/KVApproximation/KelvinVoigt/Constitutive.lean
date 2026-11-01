module

public import KVApproximation.KelvinVoigt.MaterialFields
public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Dynamics.Trajectory

/-!
# Constitutive responses for admissible materials
-/

@[expose] public section

noncomputable section

open KVApproximation.Tensor KVApproximation.Homogenization KVApproximation.Dynamics

namespace KVApproximation.KelvinVoigt

/-- Theorem 4.4: the cell constitutive model for each admissible material.
Its defining forms depend only on the two coefficient fields. -/
abbrev CellFamily (d : ℕ) (αV βV γV αE βE γE : ℝ)
    (hαV : 0 < αV) (hαE : 0 < αE) :=
  ∀ M : admissibleMaterials d αV βV γV αE βE γE,
    CellConstitutiveModel (materialViscosity hαV M) (materialElasticity hαE M)

/-- Theorem 3.1 (`eq:homogenized_model_identified`) and Theorem 4.4:
the material-point homogenized stress on the nonnegative time axis. -/
def constitutiveStress {d : ℕ} {V E : CoerciveField d}
    (C : CellConstitutiveModel V E) (e : BoundedTrajectory (Symmetric d))
    (t : ℝ) : Symmetric d :=
  action C.viscosity (e.velocity t) + action C.elasticity (e.value t) +
    ∫ s in (0 : ℝ)..t, action (C.kernel (t - s)) (e.velocity s)

end KVApproximation.KelvinVoigt
