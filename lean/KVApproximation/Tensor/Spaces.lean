module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Symmetric tensors with the Frobenius norm

The coordinate arrays carry the Euclidean inner product. Their symmetry
subspaces inherit that inner product and its norm.
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Section 2.1, tensor notation (`main.tex:171`): second-order coordinate
arrays with the Frobenius inner product. -/
abbrev SecondOrder (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)

/-- Section 2.1, tensor notation (`main.tex:171`): the symmetry condition
defining the strain and stress space `𝒱²`. -/
def symmetricSubmodule (d : ℕ) : Submodule ℝ (SecondOrder d) where
  carrier := {e | ∀ i j, e (i, j) = e (j, i)}
  zero_mem' := by simp
  add_mem' := by
    intro e f he hf i j
    change e (i, j) + f (i, j) = e (j, i) + f (j, i)
    rw [he i j, hf i j]
  smul_mem' := by
    intro r e he i j
    change r * e (i, j) = r * e (j, i)
    rw [he i j]

/-- Section 2.1 (`main.tex:171`): symmetric second-order tensors `𝒱²`,
with their inherited Frobenius norm. -/
abbrev Symmetric (d : ℕ) := symmetricSubmodule d

/-- Section 2.1 (`main.tex:171`): fourth-order coordinate arrays with
the full Frobenius inner product over all four physical indices. -/
abbrev FourthOrder (d : ℕ) :=
  EuclideanSpace ℝ ((Fin d × Fin d) × (Fin d × Fin d))

/-- Section 2.1 (`main.tex:171`): both minor symmetries and the major
symmetry of an elasticity or viscosity tensor. -/
def elasticitySubmodule (d : ℕ) : Submodule ℝ (FourthOrder d) where
  carrier := {A | ∀ i j k l,
    A ((i, j), (k, l)) = A ((j, i), (k, l)) ∧
    A ((i, j), (k, l)) = A ((i, j), (l, k)) ∧
    A ((i, j), (k, l)) = A ((k, l), (i, j))}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i j k l
    obtain ⟨hA₁, hA₂, hA₃⟩ := hA i j k l
    obtain ⟨hB₁, hB₂, hB₃⟩ := hB i j k l
    exact ⟨congrArg₂ (fun x y : ℝ => x + y) hA₁ hB₁,
      congrArg₂ (fun x y : ℝ => x + y) hA₂ hB₂,
      congrArg₂ (fun x y : ℝ => x + y) hA₃ hB₃⟩
  smul_mem' := by
    intro r A hA i j k l
    obtain ⟨h₁, h₂, h₃⟩ := hA i j k l
    change (r * _ = r * _) ∧ (r * _ = r * _) ∧ (r * _ = r * _)
    exact ⟨congrArg (r * ·) h₁, congrArg (r * ·) h₂, congrArg (r * ·) h₃⟩

/-- Section 2.1 (`main.tex:171`): fourth-order tensors `𝒱⁴` with major
and minor symmetries, equipped with the full Frobenius norm. -/
abbrev Elasticity (d : ℕ) := elasticitySubmodule d

/-- Example 2.1 (`eq:F_and_G`): dimension of the symmetric strain space. -/
def strainDimension (d : ℕ) : ℕ := d * (d + 1) / 2

/-- Example 2.1 (`eq:F_and_G`): dimension of the elasticity tensor space. -/
def elasticityDimension (d : ℕ) : ℕ :=
  strainDimension d * (strainDimension d + 1) / 2

end KVApproximation.Tensor
