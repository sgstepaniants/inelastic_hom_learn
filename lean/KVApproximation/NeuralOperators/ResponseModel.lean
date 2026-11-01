module

public import KVApproximation.NeuralOperators.Classes
public import KVApproximation.Dynamics.Trajectory
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Stress and kinetic response maps
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

/-- Section 4.1: strain, strain rate, and state, with the Euclidean
product norm used by the finite-dimensional response input. -/
abbrev StressInput (E Q : Type*) := WithLp 2 (E × WithLp 2 (E × Q))

/-- Section 4.1: strain rate and state as a Euclidean product. -/
abbrev KineticInput (E Q : Type*) := WithLp 2 (E × Q)

variable {E Q M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [TopologicalSpace M]

/-- Theorem 4.4 (`eq:learned_model_full`): stress evaluated along the
strain and internal-state trajectories. -/
def stressAlong (F : C(StressInput E Q × M, E)) (a : M)
    (e : BoundedTrajectory E) (q : BoundedTrajectory Q) (t : ℝ) : E :=
  F (WithLp.toLp 2 (e.value t, WithLp.toLp 2 (e.velocity t, q.value t)), a)

/-- Theorem 4.4 (`eq:learned_model_full`): the zero-initial-state neural
kinetic equation for one material and strain trajectory. -/
def IsResponseSolution (G : C(KineticInput E Q × M, Q)) (a : M)
    (e : BoundedTrajectory E) (q : BoundedTrajectory Q) : Prop :=
  IsKineticSolution e (fun vq => G (WithLp.toLp 2 vq, a)) q

end KVApproximation.NeuralOperators
