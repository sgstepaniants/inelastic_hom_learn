module

public import KVApproximation.Analysis.Joukowski
public import KVApproximation.Approximation.Interpolation

public section

namespace KVApproximation

/-- Lemma B.9, analytic coefficient proof: inversion preserves the Joukowski map. -/
theorem Analysis.joukowski_inv (w : ℂ) :
    joukowski w⁻¹ = joukowski w := by
  sorry

/-- Lemma B.9, analytic coefficient proof: the unit circle maps to its real part. -/
theorem Analysis.joukowski_unit {w : ℂ} (hw : ‖w‖ = 1) :
    joukowski w = (w.re : ℂ) := by
  sorry

/-- Lemma B.9, analytic coefficient proof: the closed symmetric annulus
maps into the filled Bernstein ellipse. -/
theorem Approximation.joukowski_mem_bernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ)
    {w : ℂ} (hw : ρ⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ ρ) :
    Analysis.joukowski w ∈ bernsteinEllipse ρ := by
  sorry

/-- Lemma B.9: the reference interval lies in every nondegenerate Bernstein ellipse. -/
theorem Approximation.real_mem_bernsteinEllipse {ρ : ℝ} (hρ : 1 < ρ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (x : ℂ) ∈ bernsteinEllipse ρ := by
  sorry

/-- Lemma B.9: the ellipse's imaginary coordinate is bounded by its semiaxis. -/
theorem Approximation.bernsteinEllipse_im_le {ρ : ℝ} (hρ : 1 < ρ)
    {z : ℂ} (hz : z ∈ bernsteinEllipse ρ) :
    |z.im| ≤ bernsteinImaginarySemiaxis ρ := by
  sorry

end KVApproximation
