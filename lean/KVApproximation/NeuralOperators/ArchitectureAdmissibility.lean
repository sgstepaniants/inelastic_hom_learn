module

public import KVApproximation.NeuralOperators.Classes

/-!
# Architecture regularity and approximation
-/

public section

namespace KVApproximation.NeuralOperators

/-- Remark 4.2 (`rmk:general_admissibility`): an expressive class whose
members are locally Lipschitz in the vector input satisfies A2 with the
same approximator chosen for A1. Expressivity remains an explicit premise. -/
theorem HasUniversalApproximation.locallyLipschitz
    {X M F : Type*} [PseudoMetricSpace X] [TopologicalSpace M] [NormedAddCommGroup F]
    {N : Set C(X × M, F)} (hN : HasUniversalApproximation N)
    (hlocal : ∀ Φ ∈ N, ∀ m : M, LocallyLipschitz (fun x : X => Φ (x, m))) :
    HasLocallyLipschitzApproximation N := by
  intro K L hK hL g ε hε
  obtain ⟨Φ, hΦ, herror⟩ := hN K L hK hL g ε hε
  exact ⟨Φ, hΦ, herror, fun m _ => hlocal Φ hΦ m⟩

end KVApproximation.NeuralOperators
