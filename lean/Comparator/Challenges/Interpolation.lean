module

public import KVApproximation.Approximation.Interpolation
public import KVApproximation.Approximation.LogPartition

/-!
# Interpolation and partition statements for Appendix B
-/

public section

namespace KVApproximation.Approximation

/-- Lemma B.9, proof: the generic Banach-valued root-node interpolation
estimate on a Bernstein ellipse. -/
theorem chebyshevInterpolant_error_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {ρ M : ℝ} {m : ℕ}
    (hρ : 1 < ρ) (hM : 0 ≤ M) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (bernsteinEllipse ρ))
    (hbound : ∀ z ∈ bernsteinEllipse ρ, ‖f z‖ ≤ M) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖f x - chebyshevInterpolant m f x‖ ≤ chebyshevErrorBound M ρ m := by
  sorry

/-- Definition B.8: the logarithmic hats form a partition of unity. -/
theorem sum_logHat {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ∈ Set.Icc 0 R) :
    ∑ j : Fin (logPartitionCount R), logHat R j x = 1 := by
  sorry

/-- Definition B.8: every patch has positive length and half-width at most one. -/
theorem logPatch_width {R : ℝ} (hR : 0 < R) (j : Fin (logPartitionCount R)) :
    0 < logPatchRight R j - logPatchLeft R j ∧
      (logPatchRight R j - logPatchLeft R j) / 2 ≤ 1 := by
  sorry

/-- Definition B.8: the local coordinate maps are inverse on the reference interval. -/
theorem localCoordinate_localRate {lower R : ℝ} (hlower : 0 < lower) (hR : 0 < R)
    (j : Fin (logPartitionCount R)) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    localCoordinate lower R j (localRate lower R j x) = x := by
  sorry

end KVApproximation.Approximation
