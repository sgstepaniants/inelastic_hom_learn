module

public import KVApproximation.NeuralOperators.ResponseModel
public import KVApproximation.Dynamics.PronyModel

/-!
# Compact response domains for Prony models
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

variable {E Q M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Lemma B.12 (`lem:ua_step3_no`): the strain, velocity, and state domain
with a prescribed stress budget and internal-state radius. -/
def stressInputSet (βE βV δ radius : ℝ) : Set (StressInput E Q) :=
  {x | βE * ‖(WithLp.ofLp x).1‖ +
      βV * ‖(WithLp.ofLp (WithLp.ofLp x).2).1‖ ≤ δ ∧
    ‖(WithLp.ofLp (WithLp.ofLp x).2).2‖ ≤ radius}

/-- Lemma B.12: the projected domain for the kinetic response. -/
def kineticInputSet (βV δ radius : ℝ) : Set (KineticInput E Q) :=
  {x | βV * ‖(WithLp.ofLp x).1‖ ≤ δ ∧ ‖(WithLp.ofLp x).2‖ ≤ radius}

/-- Lemma B.12: the Prony stress response in the Euclidean input coordinates. -/
def pronyStressResponse {n : ℕ} (P : PronyModel M E n) (a : M)
    (x : StressInput E (BlockState n E)) : E :=
  P.stressResponse a (WithLp.ofLp x).1
    (WithLp.ofLp (WithLp.ofLp x).2).1 (WithLp.ofLp (WithLp.ofLp x).2).2

/-- Lemma B.12: the Prony kinetic response in the Euclidean input coordinates. -/
def pronyKineticResponse {n : ℕ} (P : PronyModel M E n) (a : M)
    (x : KineticInput E (BlockState n E)) : BlockState n E :=
  P.kineticResponse a (WithLp.ofLp x).1 (WithLp.ofLp x).2

end KVApproximation.NeuralOperators
