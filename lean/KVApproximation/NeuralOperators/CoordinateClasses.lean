module

public import KVApproximation.NeuralOperators.Classes
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Response classes under a change of coordinates
-/

@[expose] public section

noncomputable section

namespace KVApproximation.NeuralOperators

variable {X X' M M' F F' : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace X']
  [TopologicalSpace M] [TopologicalSpace M']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- Lemma B.12, coordinate transport: encode both inputs, evaluate the
coordinate response, and decode its output. -/
def inducedResponse (S : X ≃ᵢ X') (U : M ≃ₜ M') (T : F ≃ₗᵢ[ℝ] F')
    (Φ : C(X' × M', F')) : C(X × M, F) :=
  ⟨fun z => T.symm (Φ (S z.1, U z.2)),
    T.symm.continuous.comp (Φ.continuous.comp
      ((S.continuous.comp continuous_fst).prodMk (U.continuous.comp continuous_snd)))⟩

/-- Lemma B.12: the response class induced by the prescribed input and
output coordinate maps. -/
def inducedResponseClass (S : X ≃ᵢ X') (U : M ≃ₜ M') (T : F ≃ₗᵢ[ℝ] F')
    (N : Set C(X' × M', F')) : Set C(X × M, F) :=
  inducedResponse S U T '' N

end KVApproximation.NeuralOperators
