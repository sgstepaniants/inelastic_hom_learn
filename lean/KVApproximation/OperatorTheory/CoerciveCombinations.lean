module

public import KVApproximation.OperatorTheory.VariationalIdentities

/-!
# Positive combinations of coercive forms
-/

@[expose] public section

noncomputable section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Theorem 3.1 and Lemma B.6: positive combinations include the transformed
coefficient form `A_s = V + s⁻¹ E`. -/
def CoerciveForm.addScaled (V E : CoerciveForm H) (c : ℝ) (hc : 0 ≤ c) :
    CoerciveForm H where
  form := V.form + c • E.form
  symmetric u v := by
    change V.form u v + c * E.form u v = V.form v u + c * E.form v u
    rw [V.symmetric u v, E.symmetric u v]
  coercive := by
    obtain ⟨a, ha, hbound⟩ := V.coercive
    refine ⟨a, ha, fun u => ?_⟩
    change _ ≤ V.form u u + c * E.form u u
    exact (hbound u).trans (le_add_of_nonneg_right (mul_nonneg hc (E.nonneg u)))

end KVApproximation.OperatorTheory
