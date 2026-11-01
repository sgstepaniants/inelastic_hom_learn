module

public import KVApproximation.Tensor.Isotropic
public import KVApproximation.Tensor.ActionBounds

/-!
# Isotropic tensor bounds in Frobenius coordinates
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.Tensor

/-- Proposition 4.7: the identity elasticity tensor acts as the identity. -/
theorem action_identityElasticity {d : ℕ} (e : Symmetric d) :
    action (identityElasticity d) e = e := by
  apply Subtype.ext
  apply PiLp.ext
  rintro ⟨i, j⟩
  change (∑ kl : Fin d × Fin d,
    ((delta i kl.1 * delta j kl.2 + delta i kl.2 * delta j kl.1) / 2) *
      e.val kl) = e.val (i, j)
  simp only [add_div, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div,
    ← Finset.sum_div, Fintype.sum_prod_type]
  simp only [delta, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [e.property j i]
  ring

/-- Appendix C.5: contraction of the volumetric tensor is the trace term. -/
theorem action_volumetricElasticity {d : ℕ} (e : Symmetric d) :
    action (volumetricElasticity d) e =
      (∑ i : Fin d, e.val (i, i)) • identityStrain d := by
  apply Subtype.ext
  apply PiLp.ext
  rintro ⟨i, j⟩
  change (∑ kl : Fin d × Fin d, (delta i j * delta kl.1 kl.2) * e.val kl) =
    (∑ k : Fin d, e.val (k, k)) * delta i j
  rw [Fintype.sum_prod_type]
  simp only [delta, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  split_ifs with hij <;> simp

/-- Appendix C.5: Frobenius pairing with the identity is the trace. -/
private theorem inner_identityStrain {d : ℕ} (e : Symmetric d) :
    ⟪e, identityStrain d⟫_ℝ = ∑ i : Fin d, e.val (i, i) := by
  change ⟪e.val, (identityStrain d).val⟫_ℝ = _
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ ij : Fin d × Fin d, delta ij.1 ij.2 * e.val ij) = _
  rw [Fintype.sum_prod_type]
  simp [delta]

/-- Appendix C.5: the identity has squared Frobenius norm equal to dimension. -/
private theorem norm_identityStrain_sq (d : ℕ) :
    ‖identityStrain d‖ ^ 2 = (d : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_identityStrain]
  simp [identityStrain, delta]

/-- Appendix C.5: isotropic contraction separates the strain and trace terms. -/
private theorem planeStress_action (young poisson : ℝ) (e : Symmetric 2) :
    action (planeStress young poisson) e =
      (young / (1 + poisson)) • e +
        (young * poisson / (1 - poisson ^ 2)) •
          (⟪e, identityStrain 2⟫_ℝ • identityStrain 2) := by
  change actionL 2 (planeStress young poisson) e = _
  rw [planeStress, map_add, map_smul, map_smul]
  simp only [add_apply, smul_apply,
    actionL_apply, action_identityElasticity, action_volumetricElasticity,
    inner_identityStrain]

/-- Appendix C.5: the volumetric and deviatoric coefficients have the stated sum. -/
private theorem planeStress_coefficients {young poisson : ℝ}
    (hPoisson : 0 ≤ poisson) (hPoissonOne : poisson < 1) :
    young / (1 + poisson) + 2 * (young * poisson / (1 - poisson ^ 2)) =
      young / (1 - poisson) := by
  have hp : 0 < 1 + poisson := by linarith
  have hm : 0 < 1 - poisson := by linarith
  have hsq : 0 < 1 - poisson ^ 2 := by nlinarith
  field_simp [hp.ne', hm.ne', hsq.ne']
  ring

/-- Appendix C.5, comparison with Section 4.1: the smallest quadratic-form
eigenvalue differs from the minimum value of the operator norm across materials. -/
theorem planeStress_bounds {young poisson : ℝ}
    (hYoung : 0 ≤ young) (hPoisson : 0 ≤ poisson) (hPoissonOne : poisson < 1) :
    HasBounds (young / (1 + poisson)) (young / (1 - poisson))
      (planeStress young poisson) := by
  have hsq : 0 < 1 - poisson ^ 2 := by nlinarith
  have hb : 0 ≤ young * poisson / (1 - poisson ^ 2) :=
    div_nonneg (mul_nonneg hYoung hPoisson) hsq.le
  intro e
  have ht : ⟪e, identityStrain 2⟫_ℝ ^ 2 ≤ 2 * ‖e‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg ⟪e, identityStrain 2⟫_ℝ) (mul_nonneg (norm_nonneg e)
      (norm_nonneg (identityStrain 2)))).2 (norm_inner_le_norm e (identityStrain 2))
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow, norm_identityStrain_sq,
      Nat.cast_ofNat, mul_comm] using h
  have henergy : ⟪e, action (planeStress young poisson) e⟫_ℝ =
      young / (1 + poisson) * ‖e‖ ^ 2 +
        young * poisson / (1 - poisson ^ 2) * ⟪e, identityStrain 2⟫_ℝ ^ 2 := by
    rw [planeStress_action, inner_add_right]
    rw [real_inner_smul_right e e, real_inner_smul_right e
      (⟪e, identityStrain 2⟫_ℝ • identityStrain 2),
      real_inner_smul_right e (identityStrain 2), real_inner_self_eq_norm_sq]
    ring
  rw [henergy]
  constructor
  · nlinarith [mul_nonneg hb (sq_nonneg ⟪e, identityStrain 2⟫_ℝ)]
  · have hcoef := planeStress_coefficients (young := young) hPoisson hPoissonOne
    nlinarith [mul_le_mul_of_nonneg_left ht hb]

/-- Appendix C.5 (`app:kv2d_modulus_ranges`): the stated operator norm on
symmetric tensors with their Frobenius norm. The sampled positive Poisson
ratios lie in this range; negative ratios require a different maximum. -/
theorem planeStress_operatorNorm {young poisson : ℝ}
    (hYoung : 0 ≤ young) (hPoisson : 0 ≤ poisson) (hPoissonOne : poisson < 1) :
    ‖actionL 2 (planeStress young poisson)‖ = young / (1 - poisson) := by
  have hp : 0 < 1 + poisson := by linarith
  have hm : 0 < 1 - poisson := by linarith
  have hc : 0 ≤ young / (1 - poisson) := div_nonneg hYoung hm.le
  apply le_antisymm
  · exact (planeStress_bounds hYoung hPoisson hPoissonOne).action_opNorm_le
      (div_nonneg hYoung hp.le) hc
  · have heigen : action (planeStress young poisson) (identityStrain 2) =
        (young / (1 - poisson)) • identityStrain 2 := by
      rw [planeStress_action, real_inner_self_eq_norm_sq, norm_identityStrain_sq,
        smul_smul, ← add_smul]
      congr 1
      simpa only [Nat.cast_ofNat, mul_comm] using
        planeStress_coefficients (young := young) hPoisson hPoissonOne
    have hnorm : 0 < ‖identityStrain 2‖ := by
      have h : ‖identityStrain 2‖ ^ 2 = (2 : ℝ) := norm_identityStrain_sq 2
      nlinarith [norm_nonneg (identityStrain 2)]
    have h := (actionL 2 (planeStress young poisson)).le_opNorm (identityStrain 2)
    rw [actionL_apply, heigen, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at h
    exact (mul_le_mul_iff_of_pos_right hnorm).mp h

end KVApproximation.Tensor
