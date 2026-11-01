module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Concatenation of Euclidean coordinate vectors
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Analysis

/-- Lemma B.12, scalar input coordinates: concatenate two Euclidean
vectors in order, preserving their Euclidean product norm. -/
def appendEuclidean (n m : ℕ) :
    WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + m)) :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)

end KVApproximation.Analysis
