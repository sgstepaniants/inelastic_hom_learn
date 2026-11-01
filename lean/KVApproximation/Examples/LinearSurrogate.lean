module

public import KVApproximation.Dynamics.PronyModel

/-!
# Tensor blocks of a fitted linear model
-/

@[expose] public section

noncomputable section

open KVApproximation.Dynamics

namespace KVApproximation.Examples.LinearSurrogate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Appendix C.6: insertion into one internal tensor block. -/
def blockInsertion {n : ℕ} (j : Fin n) (e : E) : BlockState n E :=
  WithLp.toLp 2 (Pi.single j e)

/-- Appendix C.6 (`app:kv2d_linear_fit`): the `i`th block of `S⁻¹ C`. -/
def inputBlock {n : ℕ} (S : BlockState n E ≃ₗ[ℝ] BlockState n E)
    (C : E →ₗ[ℝ] BlockState n E) (i : Fin n) (e : E) : E := (S.symm (C e)) i

/-- Appendix C.6: the `(i,j)` block of `S⁻¹ D S`. -/
def evolutionBlock {n : ℕ} (S : BlockState n E ≃ₗ[ℝ] BlockState n E)
    (D : BlockState n E →ₗ[ℝ] BlockState n E) (i j : Fin n) (e : E) : E :=
  (S.symm (D (S (blockInsertion j e)))) i

end KVApproximation.Examples.LinearSurrogate
