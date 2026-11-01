module

public import KVApproximation.Approximation.ChebyshevAnalytic
public import KVApproximation.Approximation.ChebyshevSeries
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Banach-valued interpolation on Bernstein ellipses
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
  intro x hx
  obtain ⟨φ, hφ, hvalue⟩ := exists_dual_vector'' ℂ (f x - chebyshevInterpolant m f x)
  have hanalytic : AnalyticOnNhd ℂ (fun z => φ (f z)) (bernsteinEllipse ρ) :=
    fun z hz => (φ.analyticAt (f z)).comp (hf z hz)
  have hscalar_bound (z : ℂ) (hz : z ∈ bernsteinEllipse ρ) : ‖φ (f z)‖ ≤ M := by
    calc
      ‖φ (f z)‖ ≤ ‖φ‖ * ‖f z‖ := φ.le_opNorm _
      _ ≤ 1 * ‖f z‖ := mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
      _ ≤ M := by simpa only [one_mul] using hbound z hz
  have herror := chebyshev_series_interpolation_error_le (f := fun z => φ (f z)) hρ hM hm
    (fun y hy => hasSum_chebyshevSeries hρ hM hanalytic hscalar_bound hy)
    (norm_chebyshevCoefficient_le hρ hM hanalytic hscalar_bound) hx
  have hinterp : φ (chebyshevInterpolant m f x) =
      chebyshevInterpolant m (fun z => φ (f z)) x := by
    simp only [chebyshevInterpolant, map_sum, map_smul]
  calc
    ‖f x - chebyshevInterpolant m f x‖ = ‖φ (f x - chebyshevInterpolant m f x)‖ := by
      rw [hvalue]
      simp
    _ = ‖φ (f x) - chebyshevInterpolant m (fun z => φ (f z)) x‖ := by
      rw [map_sub, hinterp]
    _ ≤ chebyshevErrorBound M ρ m := herror

end KVApproximation.Approximation
