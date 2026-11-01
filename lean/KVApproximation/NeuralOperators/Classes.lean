module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Approximation properties of response classes

The vector input, material input, and output are separate parameters. Concrete
architectures supply the class of continuous maps and prove these properties.
-/

@[expose] public section

namespace KVApproximation.NeuralOperators

variable {X M F : Type*} [PseudoMetricSpace X] [TopologicalSpace M]
  [NormedAddCommGroup F]

/-- Assumption (A1), Section 4.1 (`no:ua`): uniform approximation on every
product of compact input sets. The target is defined only on that product. -/
def HasUniversalApproximation (N : Set C(X × M, F)) : Prop :=
  ∀ (K : Set X) (L : Set M), IsCompact K → IsCompact L →
    ∀ (g : C(K × L, F)) (ε : ℝ), 0 < ε →
      ∃ Φ ∈ N, ∀ (x : K) (m : L), ‖Φ (x, m) - g (x, m)‖ ≤ ε

/-- Assumption (A2), Section 4.1 (`no:lip`): the same approximator is
locally Lipschitz in the full vector input for each material in the compact
material set. The Lipschitz constants may depend on that material. -/
def HasLocallyLipschitzApproximation (N : Set C(X × M, F)) : Prop :=
  ∀ (K : Set X) (L : Set M), IsCompact K → IsCompact L →
    ∀ (g : C(K × L, F)) (ε : ℝ), 0 < ε →
      ∃ Φ ∈ N,
        (∀ (x : K) (m : L), ‖Φ (x, m) - g (x, m)‖ ≤ ε) ∧
        ∀ m ∈ L, LocallyLipschitz (fun x : X => Φ (x, m))

end KVApproximation.NeuralOperators
