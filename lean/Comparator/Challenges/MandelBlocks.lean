module

public import KVApproximation.Tensor.MandelBlocks

/-!
# Concatenated Mandel isometries
-/

public section

namespace KVApproximation.Tensor

/-- Lemma B.11: concatenated Mandel coordinates preserve the Euclidean
block norm and give every scalar coordinate vector, including empty blocks. -/
theorem blockStrainMandel_isometry (n d : ℕ) :
    ∃ T : PiLp 2 (fun _ : Fin n => Symmetric d) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin n × StrainIndex d),
      ∀ q, T q = blockStrainMandel q := by
  sorry

/-- Lemma B.11: the scalar state norm equals the tensor block norm. -/
theorem blockStrainMandel_norm {n d : ℕ} (q : PiLp 2 (fun _ : Fin n => Symmetric d)) :
    ‖blockStrainMandel q‖ = ‖q‖ := by
  sorry

end KVApproximation.Tensor
