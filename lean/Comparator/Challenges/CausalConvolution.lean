module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Theorem 3.1, time-domain recovery: the causal convolution has
the memory-equation orientation at every nonnegative time, including zero. -/
theorem posConvolution_eq_integral_sub
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {t : ℝ} (ht : 0 ≤ t) :
    posConvolution K f L volume t = ∫ r in (0 : ℝ)..t, L (K (t - r)) (f r) := by
  sorry

/-- Theorem 3.1, memory integrability: a continuous kernel paired
with an integrable velocity is integrable at every time in the closed horizon. -/
theorem intervalIntegrable_posConvolution_integrand
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {T : ℝ} (hK : Continuous K) (hf : IntervalIntegrable f volume 0 T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun r => L (K (t - r)) (f r)) volume 0 t := by
  sorry

/-- Theorem 3.1, continuous memory term: only integrability of the
velocity is needed for continuity of its convolution with a continuous kernel. -/
theorem continuousOn_posConvolution
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {T : ℝ} (hK : Continuous K) (hf : IntervalIntegrable f volume 0 T) :
    ContinuousOn (posConvolution K f L volume) (Set.Icc (0 : ℝ) T) := by
  sorry

/-- Theorem 3.1, finite-time Fubini: a continuous kernel on a compact
rectangle and one integrable factor give a genuine product-space integral. -/
theorem integrable_rectangle_bilinear
    (L : E →L[ℝ] F →L[ℝ] G) (Φ : ℝ × ℝ → E) (f : ℝ → F)
    {T : ℝ} (hΦ : Continuous Φ) (hf : IntervalIntegrable f volume 0 T) :
    IntegrableOn (fun p : ℝ × ℝ => L (Φ p) (f p.2))
      (Set.uIoc (0 : ℝ) T ×ˢ Set.uIoc (0 : ℝ) T) := by
  sorry

/-- Theorem 3.1, integrated weak equation: Fubini on a finite triangle
exchanges the time variable and the earlier integration time. -/
theorem integral_triangle_swap [CompleteSpace G]
    (Φ : ℝ → ℝ → G) {T : ℝ} (hT : 0 ≤ T)
    (hΦ : IntegrableOn (Function.uncurry Φ)
      (Set.uIoc (0 : ℝ) T ×ˢ Set.uIoc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, ∫ r in (0 : ℝ)..t, Φ t r) =
      ∫ r in (0 : ℝ)..T, ∫ t in r..T, Φ t r := by
  sorry

/-- Theorem 3.1, Duhamel integration: finite-triangle Fubini integrates
the kernel before the forcing, without requiring completeness of the input. -/
theorem integral_posConvolution_eq_integral_kernel [CompleteSpace G]
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {T : ℝ} (hT : 0 ≤ T) (hK : Continuous K)
    (hf : IntervalIntegrable f volume 0 T) :
    (∫ t in (0 : ℝ)..T, posConvolution K f L volume t) =
      ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..(T - r), L (K s) (f r) := by
  sorry

/-- Theorem 3.1, integrated weak equation: finite-time Fubini moves
the primitive through the memory convolution without differentiating the kernel. -/
theorem integral_posConvolution_eq_posConvolution_primitive
    [CompleteSpace F] [CompleteSpace G]
    (L : E →L[ℝ] F →L[ℝ] G) (K : ℝ → E) (f : ℝ → F)
    {T : ℝ} (hT : 0 ≤ T) (hK : Continuous K)
    (hf : IntervalIntegrable f volume 0 T) :
    (∫ t in (0 : ℝ)..T, posConvolution K f L volume t) =
      posConvolution K (fun t => ∫ r in (0 : ℝ)..t, f r) L volume T := by
  sorry

end KVApproximation.Analysis
