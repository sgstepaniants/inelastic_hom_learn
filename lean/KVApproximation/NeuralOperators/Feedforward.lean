module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite feedforward networks
-/

@[expose] public section

noncomputable section

namespace KVApproximation.NeuralOperators

universe u

/-- Example 2.1 and Remarks 4.2–4.3: a finite feedforward network with
affine output. Each added layer applies a coordinate activation followed
by an affine map. The affine constructor includes linear maps exactly. -/
inductive Feedforward (E : Type u) [AddCommGroup E] [Module ℝ E] : ℕ → Type u where
  | affine {output : ℕ} (weight : E →ₗ[ℝ] EuclideanSpace ℝ (Fin output))
      (bias : EuclideanSpace ℝ (Fin output)) : Feedforward E output
  | layer {hidden output : ℕ} (previous : Feedforward E hidden)
      (weight : EuclideanSpace ℝ (Fin hidden) →ₗ[ℝ] EuclideanSpace ℝ (Fin output))
      (bias : EuclideanSpace ℝ (Fin output)) : Feedforward E output

/-- Example 2.1 and Remarks 4.2–4.3: evaluation of the finite affine and
coordinate-activation layers, including the affine-only case. -/
def Feedforward.eval {E : Type*} [AddCommGroup E] [Module ℝ E] {output : ℕ}
    (σ : ℝ → ℝ) : Feedforward E output → E → EuclideanSpace ℝ (Fin output)
  | .affine A b, x => A x + b
  | .layer previous A b, x => A (WithLp.toLp 2 (fun i => σ (previous.eval σ x i))) + b

end KVApproximation.NeuralOperators
