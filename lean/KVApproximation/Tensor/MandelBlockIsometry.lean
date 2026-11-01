module

public import KVApproximation.Tensor.MandelBlocks
public import KVApproximation.Tensor.MandelIsometry

/-!
# Concatenated Mandel isometries
-/

public section

noncomputable section

namespace KVApproximation.Tensor

/-- Lemma B.11: concatenated Mandel coordinates preserve the Euclidean
block norm and give every scalar coordinate vector, including empty blocks. -/
theorem blockStrainMandel_isometry (n d : ℕ) :
    ∃ T : PiLp 2 (fun _ : Fin n => Symmetric d) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin n × StrainIndex d),
      ∀ q, T q = blockStrainMandel q := by
  classical
  obtain ⟨T, hT⟩ := strainMandel_isometry d
  let L : PiLp 2 (fun _ : Fin n => Symmetric d) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n × StrainIndex d) :=
    { toFun := blockStrainMandel
      map_add' := by
        intro q r
        ext p
        change strainMandel (q p.1 + r p.1) p.2 =
          strainMandel (q p.1) p.2 + strainMandel (r p.1) p.2
        simp only [← hT, map_add, PiLp.add_apply]
      map_smul' := by
        intro a q
        ext p
        change strainMandel (a • q p.1) p.2 = a * strainMandel (q p.1) p.2
        simp only [← hT, map_smul, PiLp.smul_apply, smul_eq_mul]
      norm_map' := by
        intro q
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
        change (∑ p : Fin n × StrainIndex d, ‖strainMandel (q p.1) p.2‖ ^ 2) = _
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k _
        change (∑ j, ‖strainMandel (q k) j‖ ^ 2) = ‖q k‖ ^ 2
        rw [← PiLp.norm_sq_eq_of_L2 (fun _ : StrainIndex d => ℝ) (strainMandel (q k)),
          ← hT, T.norm_map] }
  have hsurj : Function.Surjective L := by
    intro x
    refine ⟨WithLp.toLp 2 (fun k => T.symm (WithLp.toLp 2 (fun p => x (k, p)))), ?_⟩
    ext p
    change strainMandel (T.symm (WithLp.toLp 2 (fun j => x (p.1, j)))) p.2 = x p
    rw [← hT, T.apply_symm_apply]
  exact ⟨LinearIsometryEquiv.ofSurjective L hsurj, fun _ => rfl⟩

/-- Lemma B.11: the scalar state norm equals the tensor block norm. -/
theorem blockStrainMandel_norm {n d : ℕ} (q : PiLp 2 (fun _ : Fin n => Symmetric d)) :
    ‖blockStrainMandel q‖ = ‖q‖ := by
  obtain ⟨T, hT⟩ := blockStrainMandel_isometry n d
  rw [← hT, T.norm_map]

end KVApproximation.Tensor
