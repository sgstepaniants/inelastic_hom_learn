module

public import KVApproximation.Tensor.Action

/-!
# Identity and volumetric tensors
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Tensor

/-- Physical-index Kronecker delta, used in the identity and isotropic tensors. -/
def delta {d : ℕ} (i j : Fin d) : ℝ := if i = j then 1 else 0

/-- Symmetry of the Kronecker delta. -/
theorem delta_symm {d : ℕ} (i j : Fin d) : delta i j = delta j i := by
  simp only [delta, eq_comm]

/-- Appendix C.5 (`app:kv2d_modulus_ranges`): the second-order identity tensor. -/
def identityStrain (d : ℕ) : Symmetric d :=
  ⟨WithLp.toLp 2 (fun ij => delta ij.1 ij.2), fun i j => delta_symm i j⟩

/-- Proposition 4.7 (`prop:no_spectral_stability`): the identity operator
on symmetric strains, written as a fourth-order tensor with both minor symmetries. -/
def identityElasticity (d : ℕ) : Elasticity d :=
  ⟨WithLp.toLp 2 (fun p =>
    (delta p.1.1 p.2.1 * delta p.1.2 p.2.2 +
      delta p.1.1 p.2.2 * delta p.1.2 p.2.1) / 2), by
    intro i j k l
    change ((delta i k * delta j l + delta i l * delta j k) / 2 =
      (delta j k * delta i l + delta j l * delta i k) / 2) ∧
      ((delta i k * delta j l + delta i l * delta j k) / 2 =
        (delta i l * delta j k + delta i k * delta j l) / 2) ∧
      ((delta i k * delta j l + delta i l * delta j k) / 2 =
        (delta k i * delta l j + delta k j * delta l i) / 2)
    refine ⟨by ring, by ring, ?_⟩
    rw [delta_symm k i, delta_symm l j, delta_symm k j, delta_symm l i]
    ring⟩

/-- Appendix C.5: the fourth-order tensor taking a strain to its trace
times the second-order identity. -/
def volumetricElasticity (d : ℕ) : Elasticity d :=
  ⟨WithLp.toLp 2 (fun p => delta p.1.1 p.1.2 * delta p.2.1 p.2.2), by
    intro i j k l
    change (delta i j * delta k l = delta j i * delta k l) ∧
      (delta i j * delta k l = delta i j * delta l k) ∧
      (delta i j * delta k l = delta k l * delta i j)
    exact ⟨by rw [delta_symm i j], by rw [delta_symm k l], mul_comm _ _⟩⟩

/-- Appendix C.5 (`app:kv2d_modulus_ranges`), with its formula in Section 5.1:
the isotropic plane-stress viscosity or elasticity tensor. -/
def planeStress (young poisson : ℝ) : Elasticity 2 :=
  (young / (1 + poisson)) • identityElasticity 2 +
    (young * poisson / (1 - poisson ^ 2)) • volumetricElasticity 2

end KVApproximation.Tensor
