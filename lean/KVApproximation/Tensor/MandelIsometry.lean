module

public import KVApproximation.Tensor.Dimensions

/-!
# Frobenius isometries of the Mandel coordinates
-/

public section

noncomputable section

namespace KVApproximation.Tensor

private theorem sum_upper_triangle {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι × ι → ℝ) (hf : ∀ i j, f (i, j) = f (j, i)) :
    (∑ p : ι × ι, f p) =
      ∑ p : {p : ι × ι // p.1 ≤ p.2}, (if p.val.1 = p.val.2 then 1 else 2) * f p.val := by
  classical
  have hswap : (∑ p : ι × ι, if p.2 < p.1 then f p else 0) =
      ∑ p : ι × ι, if p.1 < p.2 then f p else 0 := by
    apply Fintype.sum_equiv (Equiv.prodComm ι ι)
    rintro ⟨i, j⟩
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hf i j]
    rfl
  have hsplit (p : ι × ι) :
      f p = (if p.1 ≤ p.2 then f p else 0) + (if p.2 < p.1 then f p else 0) := by
    by_cases hp : p.1 ≤ p.2
    · simp [hp, not_lt.mpr hp]
    · simp [hp, lt_of_not_ge hp]
  calc
    (∑ p : ι × ι, f p) =
        (∑ p : ι × ι, if p.1 ≤ p.2 then f p else 0) +
        ∑ p : ι × ι, if p.2 < p.1 then f p else 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => hsplit p)
    _ = (∑ p : ι × ι, if p.1 ≤ p.2 then f p else 0) +
        ∑ p : ι × ι, if p.1 < p.2 then f p else 0 := by rw [hswap]
    _ = ∑ p : ι × ι, if p.1 ≤ p.2 then
        (if p.1 = p.2 then 1 else 2) * f p else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.1 ≤ p.2
      · by_cases he : p.1 = p.2
        · simp [he]
        · simp [hp, he, lt_of_le_of_ne hp he, two_mul]
      · simp [hp, not_lt.mpr (le_of_not_ge hp)]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (p := fun p : ι × ι => p.1 ≤ p.2)
        (Finset.univ.filter (fun p : ι × ι => p.1 ≤ p.2))
        (by simp) (fun p : ι × ι => (if p.1 = p.2 then 1 else 2) * f p)

private theorem mandelWeight_ne_zero {d : ℕ} (p : StrainIndex d) :
    mandelWeight p ≠ 0 := by
  unfold mandelWeight
  split_ifs
  · norm_num
  · exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

private theorem strainMandel_norm {d : ℕ} (e : Symmetric d) :
    ‖strainMandel e‖ = ‖e‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖strainMandel e‖ ^ 2 = ‖e.val‖ ^ 2
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [sum_upper_triangle (fun p => e.val p ^ 2) (fun i j => congrArg (· ^ 2) (e.property i j))]
  apply Finset.sum_congr rfl
  intro p _
  change (mandelWeight p * e.val p.val) ^ 2 = _
  rw [mul_pow]
  unfold mandelWeight
  split_ifs
  · norm_num
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Example 2.1: the prescribed second-order Mandel coordinates form a
linear isometric isomorphism, including in dimension zero. -/
theorem strainMandel_isometry (d : ℕ) :
    ∃ T : Symmetric d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (StrainIndex d),
      ∀ e, T e = strainMandel e := by
  classical
  let L : Symmetric d →ₗᵢ[ℝ] EuclideanSpace ℝ (StrainIndex d) :=
    { toFun := strainMandel
      map_add' := by
        intro e f
        ext p
        exact mul_add _ _ _
      map_smul' := by
        intro r e
        ext p
        change mandelWeight p * (r * e.val p.val) = r * (mandelWeight p * e.val p.val)
        ring
      norm_map' := strainMandel_norm }
  have hsurj : Function.Surjective L := by
    intro x
    let e : Symmetric d :=
      ⟨WithLp.toLp 2 (fun p =>
        x ⟨(min p.1 p.2, max p.1 p.2), min_le_max⟩ /
          mandelWeight ⟨(min p.1 p.2, max p.1 p.2), min_le_max⟩), by
        intro i j
        change x ⟨(min i j, max i j), _⟩ / mandelWeight ⟨(min i j, max i j), _⟩ =
          x ⟨(min j i, max j i), _⟩ / mandelWeight ⟨(min j i, max j i), _⟩
        simp only [min_comm i j, max_comm i j]⟩
    refine ⟨e, ?_⟩
    ext p
    change mandelWeight p *
      (x ⟨(min p.val.1 p.val.2, max p.val.1 p.val.2), _⟩ /
        mandelWeight ⟨(min p.val.1 p.val.2, max p.val.1 p.val.2), _⟩) = x p
    simp only [min_eq_left p.property, max_eq_right p.property]
    exact mul_div_cancel₀ _ (mandelWeight_ne_zero p)
  exact ⟨LinearIsometryEquiv.ofSurjective L hsurj, fun _ => rfl⟩

private theorem strainIndexCode_injective {d : ℕ} :
    Function.Injective (strainIndexCode (d := d)) := by
  intro p q h
  apply Subtype.ext
  apply finProdFinEquiv.injective
  apply Fin.ext
  change p.val.2.val + d * p.val.1.val = q.val.2.val + d * q.val.1.val
  simpa only [strainIndexCode, Nat.mul_comm, Nat.add_comm] using h

private abbrev strainCodeOrder (d : ℕ) : LinearOrder (StrainIndex d) :=
  LinearOrder.lift' strainIndexCode strainIndexCode_injective

/-- Example 2.1 (`eq:F_and_G`): the number of independent elasticity components. -/
theorem card_elasticityIndex (d : ℕ) :
    Fintype.card (ElasticityIndex d) = elasticityDimension d := by
  have hc : Fintype.card (ElasticityIndex d) = Fintype.card (Sym2 (StrainIndex d)) :=
    Fintype.card_congr (@Sym2.sortEquiv (StrainIndex d) (strainCodeOrder d)).symm
  rw [hc, Sym2.card,
    card_strainIndex, Nat.choose_two_right]
  simp only [Nat.add_sub_cancel, elasticityDimension, Nat.mul_comm]

private theorem sum_mandelWeight_sq {d : ℕ} (f : Fin d × Fin d → ℝ)
    (hf : ∀ i j, f (i, j) = f (j, i)) :
    (∑ ij, f ij ^ 2) = ∑ p : StrainIndex d, (mandelWeight p * f p.val) ^ 2 := by
  rw [sum_upper_triangle (fun p => f p ^ 2) (fun i j => congrArg (· ^ 2) (hf i j))]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_pow]
  unfold mandelWeight
  split_ifs
  · norm_num
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem elasticity_minor_sum {d : ℕ} (A : Elasticity d) :
    (∑ p : (Fin d × Fin d) × (Fin d × Fin d), A.val p ^ 2) =
      ∑ p : StrainIndex d × StrainIndex d,
        (mandelWeight p.1 * mandelWeight p.2 * A.val (p.1.val, p.2.val)) ^ 2 := by
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  calc
    (∑ ij : Fin d × Fin d, ∑ kl : Fin d × Fin d, A.val (ij, kl) ^ 2) =
        ∑ ij : Fin d × Fin d, ∑ q : StrainIndex d,
          (mandelWeight q * A.val (ij, q.val)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro ij _
      exact sum_mandelWeight_sq _ (fun k l => (A.property ij.1 ij.2 k l).2.1)
    _ = ∑ q : StrainIndex d, ∑ ij : Fin d × Fin d,
          (mandelWeight q * A.val (ij, q.val)) ^ 2 := Finset.sum_comm
    _ = ∑ q : StrainIndex d, ∑ p : StrainIndex d,
          (mandelWeight p * (mandelWeight q * A.val (p.val, q.val))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q _
      exact sum_mandelWeight_sq _ (fun i j =>
        congrArg (mandelWeight q * ·) (A.property i j q.val.1 q.val.2).1)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [mul_assoc]

private theorem elasticityMandel_norm {d : ℕ} (A : Elasticity d) :
    ‖elasticityMandel A‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖elasticityMandel A‖ ^ 2 = ‖A.val‖ ^ 2
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [elasticity_minor_sum A]
  have hs (p q : StrainIndex d) :
      (mandelWeight p * mandelWeight q * A.val (p.val, q.val)) ^ 2 =
      (mandelWeight q * mandelWeight p * A.val (q.val, p.val)) ^ 2 := by
    rw [(A.property p.val.1 p.val.2 q.val.1 q.val.2).2.2, mul_comm (mandelWeight p)]
  rw [@sum_upper_triangle (StrainIndex d) _ (strainCodeOrder d) _ hs]
  apply Finset.sum_congr rfl
  intro p _
  dsimp only [elasticityMandel, PiLp.toLp_apply]
  rw [mul_assoc, mul_assoc, mul_pow]
  split_ifs
  · simp only [one_pow, one_mul, mul_assoc]
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [mul_assoc]

/-- Example 2.1: the prescribed fourth-order coordinates preserve the full
physical-index Frobenius norm, including all minor and major multiplicities. -/
theorem elasticityMandel_isometry (d : ℕ) :
    ∃ T : Elasticity d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ElasticityIndex d),
      ∀ A, T A = elasticityMandel A := by
  classical
  let L : Elasticity d →ₗᵢ[ℝ] EuclideanSpace ℝ (ElasticityIndex d) :=
    { toFun := elasticityMandel
      map_add' := by
        intro A B
        ext p
        exact mul_add _ _ _
      map_smul' := by
        intro a A
        ext p
        change ((if p.val.1 = p.val.2 then 1 else Real.sqrt 2) *
            mandelWeight p.val.1 * mandelWeight p.val.2) *
              (a * A.val (p.val.1.val, p.val.2.val)) =
          a * (((if p.val.1 = p.val.2 then 1 else Real.sqrt 2) *
            mandelWeight p.val.1 * mandelWeight p.val.2) * A.val (p.val.1.val, p.val.2.val))
        ring
      norm_map' := elasticityMandel_norm }
  have hsurj : Function.Surjective L := by
    intro x
    let minor (i j : Fin d) : StrainIndex d := ⟨(min i j, max i j), min_le_max⟩
    have hminor_comm (i j : Fin d) : minor i j = minor j i := by
      apply Subtype.ext
      simp only [minor, min_comm i j, max_comm i j]
    have hminor_id (p : StrainIndex d) : minor p.val.1 p.val.2 = p := by
      apply Subtype.ext
      simp only [minor, min_eq_left p.property, max_eq_right p.property]
    let major (p q : StrainIndex d) : ElasticityIndex d :=
      if h : strainIndexCode p ≤ strainIndexCode q then ⟨(p, q), h⟩
      else ⟨(q, p), le_of_not_ge h⟩
    have hmajor_comm (p q : StrainIndex d) : major p q = major q p := by
      by_cases hpq : strainIndexCode p ≤ strainIndexCode q
      · by_cases hqp : strainIndexCode q ≤ strainIndexCode p
        · have heq : p = q := strainIndexCode_injective (le_antisymm hpq hqp)
          subst q
          rfl
        · simp only [major, dite_eq_left hpq, dite_eq_right hqp]
      · simp only [major, dite_eq_right hpq, dite_eq_left (le_of_not_ge hpq)]
    have hmajor_id (p : ElasticityIndex d) : major p.val.1 p.val.2 = p := by
      simp only [major, dite_eq_left p.property]
    let g (p q : StrainIndex d) : ℝ := x (major p q) / (if p = q then 1 else Real.sqrt 2)
    have hg (p q : StrainIndex d) : g p q = g q p := by
      dsimp only [g]
      rw [hmajor_comm p q]
      by_cases hp : p = q <;> simp [hp, eq_comm]
    let a (ij kl : Fin d × Fin d) : ℝ :=
      g (minor ij.1 ij.2) (minor kl.1 kl.2) /
        (mandelWeight (minor ij.1 ij.2) * mandelWeight (minor kl.1 kl.2))
    let A : Elasticity d := ⟨WithLp.toLp 2 (fun p => a p.1 p.2), by
      intro i j k l
      change (a (i, j) (k, l) = a (j, i) (k, l)) ∧
        (a (i, j) (k, l) = a (i, j) (l, k)) ∧
        (a (i, j) (k, l) = a (k, l) (i, j))
      dsimp only [a]
      refine ⟨?_, ?_, ?_⟩
      · rw [hminor_comm i j]
      · rw [hminor_comm k l]
      · rw [hg (minor i j) (minor k l), mul_comm (mandelWeight (minor i j))]⟩
    refine ⟨A, ?_⟩
    ext p
    change ((if p.val.1 = p.val.2 then 1 else Real.sqrt 2) *
      mandelWeight p.val.1 * mandelWeight p.val.2) * a p.val.1.val p.val.2.val = x p
    dsimp only [a]
    simp only [hminor_id, g, hmajor_id]
    have hw : (if p.val.1 = p.val.2 then 1 else Real.sqrt 2) ≠ 0 := by
      split_ifs
      · norm_num
      · exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp [hw, mandelWeight_ne_zero p.val.1, mandelWeight_ne_zero p.val.2]
  exact ⟨LinearIsometryEquiv.ofSurjective L hsurj, fun _ => rfl⟩

end KVApproximation.Tensor
