module

public import KVApproximation.Tensor.MandelCoordinates

/-!
# Concatenated Mandel coordinates
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Lemma B.11 (`lem:ua_step3_targets`): concatenate the prescribed
Mandel vectors of the tensorial internal variables. -/
def blockStrainMandel {n d : ℕ} (q : PiLp 2 (fun _ : Fin n => Symmetric d)) :
    EuclideanSpace ℝ (Fin n × StrainIndex d) :=
  WithLp.toLp 2 (fun p => strainMandel (q p.1) p.2)

end KVApproximation.Tensor
