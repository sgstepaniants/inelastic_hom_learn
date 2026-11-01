module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Real spectral edges of bounded operators
-/

@[expose] public section

noncomputable section

namespace KVApproximation.OperatorTheory

/-- Proposition 4.7: supremum of the real operator spectrum. For relaxation
operators on a nontrivial complete space, nonemptiness and compactness follow
from weighted self-adjointness and boundedness. -/
def upperSpectralEdge {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (R : H →L[ℝ] H) : ℝ := sSup (spectrum ℝ R)

end KVApproximation.OperatorTheory
