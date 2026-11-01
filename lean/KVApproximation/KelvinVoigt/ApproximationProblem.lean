module

public import KVApproximation.KelvinVoigt.Constitutive
public import KVApproximation.NeuralOperators.ResponseModel
public import KVApproximation.Approximation.Dimension

/-!
# Uniform constitutive approximation and state dimension
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Dynamics KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

/-- Theorem 4.4: the scalar internal-state space of dimension `nξ`. -/
abbrev InternalState (nξ : ℕ) := EuclideanSpace ℝ (Fin nξ)

/-- Section 4.1: the stress-response class in tensor coordinates.
Mandel isometries identify these coordinates with the paper's Euclidean inputs. -/
abbrev StressResponseClass (d nξ : ℕ) :=
  Set C(StressInput (Symmetric d) (InternalState nξ) × Material d, Symmetric d)

/-- Section 4.1: the kinetic-response class in tensor coordinates. -/
abbrev KineticResponseClass (d nξ : ℕ) :=
  Set C(KineticInput (Symmetric d) (InternalState nξ) × Material d, InternalState nξ)

/-- Theorem 4.4 (`eq:ua`): a single pair of responses gives a unique
bounded internal trajectory and the prescribed all-time essential-supremum
stress error for every admissible material and strain. -/
def UniformlyApproximates {d nξ : ℕ} {αV βV γV αE βE γE : ℝ}
    {hαV : 0 < αV} {hαE : 0 < αE}
    (C : CellFamily d αV βV γV αE βE γE hαV hαE)
    (F : C(StressInput (Symmetric d) (InternalState nξ) × Material d, Symmetric d))
    (G : C(KineticInput (Symmetric d) (InternalState nξ) × Material d, InternalState nξ))
    (δ ε : ℝ) : Prop :=
  ∀ (M : admissibleMaterials d αV βV γV αE βE γE)
    (e : BoundedTrajectory (Symmetric d)), e.Admissible βE βV δ →
      ∃ q : BoundedTrajectory (InternalState nξ),
        IsResponseSolution G M.val e q ∧
        (∀ q' : BoundedTrajectory (InternalState nξ),
          IsResponseSolution G M.val e q' → q'.Agree q) ∧
        eLpNorm (fun t => stressAlong F M.val e q t - constitutiveStress (C M) e t)
          ⊤ timeMeasure ≤ ENNReal.ofReal ε

/-- Theorem 4.5: the sufficient scalar state dimension, including the
singleton spectral interval as a separate exact case. -/
def sufficientDimension (d : ℕ) (R relativeError : ℝ) : ℕ :=
  if R = 0 then strainDimension d
  else Approximation.nonsingletonStateDimension (strainDimension d) R relativeError

end KVApproximation.KelvinVoigt
