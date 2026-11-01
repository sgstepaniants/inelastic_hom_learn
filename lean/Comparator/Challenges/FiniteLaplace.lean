module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.7, analyticity argument: a finite-time exponential convolution
of a Bochner-integrable function is entire in its complex rate. -/
theorem finiteLaplace_entire {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (f : ℝ → F) {t : ℝ} (ht : 0 ≤ t) (hf : IntervalIntegrable f volume 0 t) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => ∫ s in (0 : ℝ)..t, Complex.exp (-z * ((t - s : ℝ) : ℂ)) • f s)
      Set.univ := by
  sorry

end KVApproximation.Analysis
