module

public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.Analysis.Convolution

/-!
# Laplace transforms of causal convolutions
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Theorem 3.1, Laplace-domain recovery: exponential weighting
commutes with causal convolution through its two bilinear factors. -/
private theorem exponential_weight_posConvolution
    (L : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) (s t : ℝ) :
    Real.exp (-s * t) • posConvolution f g L volume t =
      posConvolution (fun r => Real.exp (-s * r) • f r)
        (fun r => Real.exp (-s * r) • g r) L volume t := by
  unfold posConvolution
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (s := Set.Ioi (0 : ℝ)) ht,
      Set.indicator_of_mem (s := Set.Ioi (0 : ℝ)) ht,
      ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro r hr
    have hexp : Real.exp (-s * (t - r)) * Real.exp (-s * r) = Real.exp (-s * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [map_smul, smul_apply, smul_smul, hexp]
  · rw [Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) ht,
      Set.indicator_of_notMem (s := Set.Ioi (0 : ℝ)) ht, smul_zero]

/-- Theorem 3.1, Laplace-domain recovery: exponentially integrable
Banach-valued factors give a genuinely integrable causal convolution.
The rate may be any real number for which the stated integrability holds. -/
theorem integrable_halfLineLaplace_posConvolution
    (L : E →L[ℝ] F →L[ℝ] G) (f : ℝ → E) (g : ℝ → F) (s : ℝ)
    (hf : IntegrableOn (fun t => Real.exp (-s * t) • f t) (Set.Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun t => Real.exp (-s * t) • g t) (Set.Ioi (0 : ℝ))) :
    IntegrableOn (fun t => Real.exp (-s * t) • posConvolution f g L volume t)
      (Set.Ioi (0 : ℝ)) := by
  have h : IntegrableOn
      (posConvolution (fun t => Real.exp (-s * t) • f t)
        (fun t => Real.exp (-s * t) • g t) L volume) (Set.Ioi (0 : ℝ)) :=
    (integrable_posConvolution hf hg L).integrableOn
  exact h.congr (Filter.Eventually.of_forall fun t =>
    (exponential_weight_posConvolution L f g s t).symm)

/-- Theorem 3.1, Laplace-domain recovery: the Bochner transform of a
causal convolution equals the continuous bilinear pairing of the transforms. -/
theorem halfLineLaplace_posConvolution [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace G] (L : E →L[ℝ] F →L[ℝ] G)
    (f : ℝ → E) (g : ℝ → F) (s : ℝ)
    (hf : IntegrableOn (fun t => Real.exp (-s * t) • f t) (Set.Ioi (0 : ℝ)))
    (hg : IntegrableOn (fun t => Real.exp (-s * t) • g t) (Set.Ioi (0 : ℝ))) :
    halfLineLaplace (posConvolution f g L volume) s =
      L (halfLineLaplace f s) (halfLineLaplace g s) := by
  unfold halfLineLaplace
  calc
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * t) • posConvolution f g L volume t) =
        ∫ t in Set.Ioi (0 : ℝ), posConvolution
          (fun r => Real.exp (-s * r) • f r) (fun r => Real.exp (-s * r) • g r) L volume t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (exponential_weight_posConvolution L f g s)
    _ = ∫ t in Set.Ioi (0 : ℝ), ∫ r in (0 : ℝ)..t,
        L (Real.exp (-s * r) • f r) (Real.exp (-s * (t - r)) • g (t - r)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact Set.indicator_of_mem ht _
    _ = _ := integral_posConvolution hf hg L

end KVApproximation.Analysis
