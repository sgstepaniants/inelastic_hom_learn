module

public import KVApproximation.Tensor.MandelFiniteIndices

/-!
# Scalar Mandel state coordinates
-/

public section

namespace KVApproximation.Tensor

/-- Example 2.1 and Lemma B.12: scalar strain Mandel coordinates give
a linear isometry onto the Euclidean space of the stated dimension. -/
theorem scalarStrainMandel_isometry (d : ℕ) :
    ∃ T : Symmetric d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (strainDimension d)),
      ∀ e, T e = scalarStrainMandel e := by
  sorry

/-- Example 2.1 and Lemma B.12: scalar elasticity Mandel coordinates
give a linear isometry with all Frobenius symmetry weights retained. -/
theorem scalarElasticityMandel_isometry (d : ℕ) :
    ∃ T : Elasticity d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (elasticityDimension d)),
      ∀ A, T A = scalarElasticityMandel A := by
  sorry

/-- Lemma B.12: reindexing the prescribed block Mandel map gives a
linear isometric equivalence with the exact scalar state space. -/
theorem scalarBlockStrainMandel_isometry (n d : ℕ) :
    ∃ T : PiLp 2 (fun _ : Fin n => Symmetric d) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n * strainDimension d)),
      ∀ q, T q = scalarBlockStrainMandel q := by
  sorry

/-- Lemmas B.11–B.12: scalar state coordinates preserve the Euclidean
block norm, including empty blocks and dimension zero. -/
theorem scalarBlockStrainMandel_norm {n d : ℕ}
    (q : PiLp 2 (fun _ : Fin n => Symmetric d)) :
    ‖scalarBlockStrainMandel q‖ = ‖q‖ := by
  sorry

end KVApproximation.Tensor
