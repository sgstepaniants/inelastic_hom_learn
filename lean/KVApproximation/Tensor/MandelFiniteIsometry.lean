module

public import KVApproximation.Tensor.MandelFiniteIndices
public import KVApproximation.Tensor.MandelBlockIsometry

/-!
# Isometry of scalar Mandel state coordinates
-/

public section

namespace KVApproximation.Tensor

/-- Example 2.1 and Lemma B.12: scalar strain Mandel coordinates give
a linear isometry onto the Euclidean space of the stated dimension. -/
theorem scalarStrainMandel_isometry (d : ℕ) :
    ∃ T : Symmetric d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (strainDimension d)),
      ∀ e, T e = scalarStrainMandel e := by
  obtain ⟨T, hT⟩ := strainMandel_isometry d
  refine ⟨T.trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (strainIndexEquivFin d)), ?_⟩
  intro e
  rw [LinearIsometryEquiv.trans_apply, hT]
  rfl

/-- Example 2.1 and Lemma B.12: scalar elasticity Mandel coordinates
give a linear isometry with all Frobenius symmetry weights retained. -/
theorem scalarElasticityMandel_isometry (d : ℕ) :
    ∃ T : Elasticity d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (elasticityDimension d)),
      ∀ A, T A = scalarElasticityMandel A := by
  obtain ⟨T, hT⟩ := elasticityMandel_isometry d
  refine ⟨T.trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (elasticityIndexEquivFin d)), ?_⟩
  intro A
  rw [LinearIsometryEquiv.trans_apply, hT]
  rfl

/-- Lemma B.12: reindexing the prescribed block Mandel map gives a
linear isometric equivalence with the exact scalar state space. -/
theorem scalarBlockStrainMandel_isometry (n d : ℕ) :
    ∃ T : PiLp 2 (fun _ : Fin n => Symmetric d) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n * strainDimension d)),
      ∀ q, T q = scalarBlockStrainMandel q := by
  obtain ⟨T, hT⟩ := blockStrainMandel_isometry n d
  refine ⟨T.trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (blockMandelIndexEquiv n d)), ?_⟩
  intro q
  rw [LinearIsometryEquiv.trans_apply, hT]
  rfl

/-- Lemmas B.11–B.12: scalar state coordinates preserve the Euclidean
block norm, including empty blocks and dimension zero. -/
theorem scalarBlockStrainMandel_norm {n d : ℕ}
    (q : PiLp 2 (fun _ : Fin n => Symmetric d)) :
    ‖scalarBlockStrainMandel q‖ = ‖q‖ := by
  obtain ⟨T, hT⟩ := scalarBlockStrainMandel_isometry n d
  rw [← hT q, T.norm_map]

end KVApproximation.Tensor
