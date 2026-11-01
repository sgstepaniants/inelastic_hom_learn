module

public import KVApproximation.Tensor.MandelCoordinates
public import Mathlib.Order.Sym2
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimensions of the physical tensor spaces

Upper triangular coordinates identify symmetric strains with independent
scalar entries. Counting sorted unordered pairs gives the dimension factor
used in Appendix A.2.
-/

public section

noncomputable section

namespace KVApproximation.Tensor

/-- Example 2.1 (`eq:F_and_G`): the number of independent strain components. -/
theorem card_strainIndex (d : ℕ) : Fintype.card (StrainIndex d) = strainDimension d := by
  rw [← Fintype.card_congr (Sym2.sortEquiv (α := Fin d)), Sym2.card,
    Fintype.card_fin, Nat.choose_two_right]
  simp only [Nat.add_sub_cancel, strainDimension, Nat.mul_comm]

/-- Section 2.1: independent upper triangular coordinates determine every strain. -/
private def strainCoordinates (d : ℕ) : Symmetric d ≃ₗ[ℝ] (StrainIndex d → ℝ) := by
  let L : Symmetric d →ₗ[ℝ] (StrainIndex d → ℝ) :=
    { toFun := fun e p => e.val p.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearEquiv.ofBijective L
  constructor
  · intro e f hef
    apply Subtype.ext
    apply PiLp.ext
    rintro ⟨i, j⟩
    rcases le_total i j with hij | hji
    · exact congrFun hef ⟨(i, j), hij⟩
    · calc
        e.val (i, j) = e.val (j, i) := e.property i j
        _ = f.val (j, i) := congrFun hef ⟨(j, i), hji⟩
        _ = f.val (i, j) := f.property j i
  · intro x
    let e : Symmetric d :=
      ⟨WithLp.toLp 2 (fun p => x ⟨(min p.1 p.2, max p.1 p.2), min_le_max⟩), by
        intro i j
        change x ⟨(min i j, max i j), _⟩ = x ⟨(min j i, max j i), _⟩
        congr 2; simp [min_comm, max_comm]⟩
    refine ⟨e, ?_⟩
    funext p
    change x ⟨(min p.val.1 p.val.2, max p.val.1 p.val.2), _⟩ = x p
    congr 1
    apply Subtype.ext
    simp only [min_eq_left p.property, max_eq_right p.property]

/-- Section 2.1 and Appendix A.2: the actual Frobenius strain space has
the dimension used in the spectral variation bound. -/
theorem finrank_symmetric (d : ℕ) :
    Module.finrank ℝ (Symmetric d) = strainDimension d := by
  rw [(strainCoordinates d).finrank_eq, Module.finrank_pi, card_strainIndex]

end KVApproximation.Tensor
