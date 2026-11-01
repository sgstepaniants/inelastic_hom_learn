module

public import Mathlib.Analysis.Convolution

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {F H Y : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel's memory term:
finite-triangle Fubini exchanges a continuous operator kernel with the
causal integral of an L¹ forcing. -/
theorem integral_operatorConvolution_assoc
    (A : ℝ → H →L[ℝ] Y) (G : ℝ → F →L[ℝ] H) (f : ℝ → F)
    {T : ℝ} (hT : 0 ≤ T) (hA : Continuous A) (hG : Continuous G)
    (hf : IntervalIntegrable f volume 0 T) :
    (∫ s in (0 : ℝ)..T, A (T - s) (∫ r in (0 : ℝ)..s, G (s - r) (f r))) =
      ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..(T - r),
        A (T - r - s) (G s (f r)) := by
  sorry

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), forced integrated
equation: causal integration of the constant-load Green balance gives
the memory equation for arbitrary L¹ forcing, without differentiating a kernel. -/
theorem duhamel_integrated_memory_balance
    (V E : H →L[ℝ] Y) (K : ℝ → H →L[ℝ] Y)
    (G : ℝ → F →L[ℝ] H) (B : F →L[ℝ] Y)
    (hK : Continuous K) (hG : Continuous G)
    (hbalance : ∀ (t : ℝ), 0 ≤ t → ∀ g : F,
      V (G t g) + E (∫ s in (0 : ℝ)..t, G s g) +
        (∫ s in (0 : ℝ)..t, K (t - s) (G s g)) = B g)
    (f : ℝ → F) {T : ℝ} (hf : IntervalIntegrable f volume 0 T) :
    let q : ℝ → H := fun t => ∫ r in (0 : ℝ)..t, G (t - r) (f r)
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      V (q t) + E (∫ s in (0 : ℝ)..t, q s) +
        (∫ s in (0 : ℝ)..t, K (t - s) (q s)) = ∫ r in (0 : ℝ)..t, B (f r) := by
  sorry

end KVApproximation.Analysis
