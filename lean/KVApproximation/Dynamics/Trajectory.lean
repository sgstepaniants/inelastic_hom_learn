module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Bounded trajectories on the nonnegative time axis

Trajectories are recorded by a representative and its velocity. The integral
identity fixes the representative, including its value at the initial time.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Dynamics

/-- Section 4.1 (`eq:admissible_strain`): Lebesgue measure on the entire
nonnegative time axis. -/
def timeMeasure : Measure ℝ := volume.restrict (Set.Ici 0)

/-- Section 4.1 (`eq:admissible_strain`), integral representation of a
`W¹,∞` trajectory on the nonnegative time axis. Values at negative times
are immaterial. -/
structure BoundedTrajectory (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] where
  value : ℝ → E
  velocity : ℝ → E
  value_memLp : MemLp value ⊤ timeMeasure
  velocity_memLp : MemLp velocity ⊤ timeMeasure
  integral_eq : ∀ t : ℝ, 0 ≤ t → value t = value 0 + ∫ s in (0 : ℝ)..t, velocity s

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Section 4.1 (`eq:admissible_strain`): essential supremum of the
trajectory's value norm. -/
def BoundedTrajectory.valueBound (e : BoundedTrajectory E) : ℝ :=
  (eLpNorm e.value ⊤ timeMeasure).toReal

/-- Section 4.1 (`eq:admissible_strain`): essential supremum of the
trajectory's velocity norm. -/
def BoundedTrajectory.velocityBound (e : BoundedTrajectory E) : ℝ :=
  (eLpNorm e.velocity ⊤ timeMeasure).toReal

/-- Section 4.1 (`eq:admissible_strain`): the combined stress-scale
constraint on the value and velocity of a strain trajectory. -/
def BoundedTrajectory.Admissible (e : BoundedTrajectory E)
    (elasticityUpper viscosityUpper stressScale : ℝ) : Prop :=
  elasticityUpper * e.valueBound + viscosityUpper * e.velocityBound ≤ stressScale

/-- Proposition B.13 (`prop:ua_step3_stability`): equality of trajectories
on the half-line, with velocities identified almost everywhere. -/
def BoundedTrajectory.Agree (e f : BoundedTrajectory E) : Prop :=
  (∀ t : ℝ, 0 ≤ t → e.value t = f.value t) ∧
    e.velocity =ᵐ[timeMeasure] f.velocity

/-- Proposition B.13 (`prop:ua_step3_stability`): an internal-variable
initial-value problem, interpreted almost everywhere in time. -/
def IsKineticSolution {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [CompleteSpace Q] (e : BoundedTrajectory E) (G : E × Q → Q)
    (q : BoundedTrajectory Q) : Prop :=
  q.value 0 = 0 ∧ ∀ᵐ t ∂timeMeasure, q.velocity t = G (e.velocity t, q.value t)

end KVApproximation.Dynamics
