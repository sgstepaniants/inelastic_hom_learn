module

public import KVApproximation.Tensor.Spaces
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Symmetric parts of second-order tensors
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Section 2.1 (`eq:strain_corrector`): the symmetric part of a
physical-index displacement gradient. -/
def symmetrize {d : ℕ} (g : SecondOrder d) : Symmetric d :=
  ⟨WithLp.toLp 2 (fun ij => (g ij + g (ij.2, ij.1)) / 2), by
    intro i j
    exact congrArg (fun z : ℝ => z / 2) (add_comm _ _)⟩

/-- Section 3.1 (`eq:space_strain_corrector`): symmetrization as a
bounded linear map for the Frobenius norms. -/
def symmetrizeL (d : ℕ) : SecondOrder d →L[ℝ] Symmetric d :=
  LinearMap.toContinuousLinearMap
    { toFun := symmetrize
      map_add' := by
        intro g h
        apply Subtype.ext
        apply PiLp.ext
        intro ij
        change ((g ij + h ij) + (g (ij.2, ij.1) + h (ij.2, ij.1))) / 2 =
          (g ij + g (ij.2, ij.1)) / 2 + (h ij + h (ij.2, ij.1)) / 2
        ring
      map_smul' := by
        intro r g
        apply Subtype.ext
        apply PiLp.ext
        intro ij
        change (r * g ij + r * g (ij.2, ij.1)) / 2 =
          r * ((g ij + g (ij.2, ij.1)) / 2)
        ring }

end KVApproximation.Tensor
