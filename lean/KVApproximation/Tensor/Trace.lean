module

public import KVApproximation.Tensor.Action

/-!
# Trace of an elasticity tensor
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Appendix A.2: the operator trace on symmetric strains. The minor
symmetries make this physical-index contraction equal to the Mandel trace. -/
def tensorTrace {d : ℕ} (A : Elasticity d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, A.val ((i, j), (i, j))

end KVApproximation.Tensor
