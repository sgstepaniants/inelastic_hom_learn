module

public import KVApproximation.Homogenization.StaticCellOperators

/-!
# Stress of a static periodic corrector
-/

@[expose] public section

noncomputable section

open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, static oscillating fluxes: coefficient multiplication
applied to the constant strain minus its weighted corrector projection. -/
def cellFlux {d : ℕ} (A : CoerciveField d) (e : Symmetric d) : StrainField d :=
  multiplication A.field
    (constantStrainL d e - (cellProjection A (constantStrainL d e) : StrainField d))

end KVApproximation.Homogenization
