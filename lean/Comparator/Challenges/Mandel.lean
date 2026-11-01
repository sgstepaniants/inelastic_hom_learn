module

public import KVApproximation.Tensor.MandelCoordinates

/-!
# Dimensions and isometries of Mandel coordinates
-/

public section

namespace KVApproximation.Tensor

/-- Example 2.1 (`eq:F_and_G`): the number of independent strain components. -/
theorem card_strainIndex (d : ℕ) : Fintype.card (StrainIndex d) = strainDimension d := by
  sorry

/-- Section 2.1 and Appendix A.2: the actual Frobenius strain space has
the dimension used in the spectral variation bound. -/
theorem finrank_symmetric (d : ℕ) :
    Module.finrank ℝ (Symmetric d) = strainDimension d := by
  sorry

/-- Example 2.1 (`eq:F_and_G`): the number of independent elasticity components. -/
theorem card_elasticityIndex (d : ℕ) :
    Fintype.card (ElasticityIndex d) = elasticityDimension d := by
  sorry

/-- Example 2.1: the prescribed second-order Mandel coordinates form a
linear isometric isomorphism, including in dimension zero. -/
theorem strainMandel_isometry (d : ℕ) :
    ∃ T : Symmetric d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (StrainIndex d),
      ∀ e, T e = strainMandel e := by
  sorry

/-- Example 2.1: the prescribed fourth-order coordinates preserve the full
physical-index Frobenius norm, including all minor and major multiplicities. -/
theorem elasticityMandel_isometry (d : ℕ) :
    ∃ T : Elasticity d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ElasticityIndex d),
      ∀ A, T A = elasticityMandel A := by
  sorry

end KVApproximation.Tensor
