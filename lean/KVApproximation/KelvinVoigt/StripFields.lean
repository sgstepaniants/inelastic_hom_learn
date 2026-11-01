module

public import KVApproximation.Analysis.PeriodicCell
public import KVApproximation.Tensor.Isotropic

/-!
# Thin-strip coefficient fields
-/

@[expose] public section

noncomputable section

open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7, proof: the thin strip of width `1/(m+1)` in coordinate
`i`. The shifted natural index includes precisely the paper's positive indices. -/
def thinStrip {d : ℕ} (i : Fin d) (m : ℕ) : Set (PeriodicCell d) :=
  {y | 0 < cellRepresentative y i ∧ cellRepresentative y i < 1 / ((m : ℝ) + 1)}

/-- Proposition 4.7, proof: the strip's elasticity field; viscosity stays equal
to the identity. The values of the elasticity coefficient are one and two. -/
def stripElasticity {d : ℕ} (i : Fin d) (m : ℕ) (y : PeriodicCell d) : Elasticity d := by
  classical
  exact (1 + if y ∈ thinStrip i m then (1 : ℝ) else 0) • identityElasticity d


end KVApproximation.KelvinVoigt
