module

public import KVApproximation.Analysis.PeriodicSobolev
public import KVApproximation.Tensor.Fields
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# The periodic strain-corrector space
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Section 3.1 (`eq:space_strain_corrector`): the closed strain-corrector
subspace. The periodic Korn theorem identifies it with the symmetric-gradient
range itself. -/
def correctorSubspace (d : ℕ) : ClosedSubmodule ℝ (StrainField d) :=
  (LinearMap.range (correctorGradientL d).toLinearMap).closure

instance (d : ℕ) : InnerProductSpace ℝ (correctorSubspace d).toSubmodule :=
  Submodule.innerProductSpace (𝕜 := ℝ) (E := StrainField d) (correctorSubspace d).toSubmodule

instance (d : ℕ) : CompleteSpace (correctorSubspace d).toSubmodule :=
  (correctorSubspace d).isClosed.completeSpace_coe

instance (d : ℕ) : NormedAddCommGroup (correctorSubspace d) :=
  inferInstanceAs (NormedAddCommGroup (correctorSubspace d).toSubmodule)

instance (d : ℕ) : InnerProductSpace ℝ (correctorSubspace d) :=
  inferInstanceAs (InnerProductSpace ℝ (correctorSubspace d).toSubmodule)

instance (d : ℕ) : CompleteSpace (correctorSubspace d) :=
  inferInstanceAs (CompleteSpace (correctorSubspace d).toSubmodule)

/-- Section 3.1: constant macroscopic strains embedded in the normalized
periodic L² space. -/
def constantStrainL (d : ℕ) : Symmetric d →L[ℝ] StrainField d :=
  Lp.constL 2 (cellMeasure d) ℝ

end KVApproximation.Homogenization
