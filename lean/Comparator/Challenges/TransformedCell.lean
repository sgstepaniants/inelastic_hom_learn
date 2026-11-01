module

public import KVApproximation.Homogenization.CellOperators
public import KVApproximation.Tensor.FieldCombinations
public import KVApproximation.OperatorTheory.SpectralBounds
public import KVApproximation.Analysis.HalfLineLaplaceProperties

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Theorem 3.1, transformed cell equation: the effective form of the
actual coefficient V + s⁻¹ E is the sum of the two static forms and the
compressed relaxation resolvent. -/
theorem effectiveForm_addSMul_resolvent {d : ℕ} (V E : CoerciveField d)
    {s : ℝ} (hs : 0 < s) (e f : Symmetric d) :
    effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le)) e f =
      effectiveForm V e f + s⁻¹ * effectiveForm E e f +
        ⟪cfc (fun r : ℝ => r / (s + r))
          (weightedRelaxation V.toForm E.toForm (correctorSubspace d))
          (weightedMismatch V.toForm E.toForm (correctorSubspace d) (constantStrainL d) e),
          weightedMismatch V.toForm E.toForm (correctorSubspace d) (constantStrainL d) f⟫_ℝ := by
  sorry

/-- Theorem 3.1, Laplace transform of the memory kernel: the actual
tensor-valued cell kernel is Bochner integrable against every positive-rate
exponential on the whole positive time axis. -/
theorem cellKernel_integrable_halfLineLaplace {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) • C.kernel t) (Set.Ioi (0 : ℝ)) := by
  sorry

/-- Theorem 3.1, constitutive identification in the proof following
`eq:homogenized_model_identified`: the effective combined coefficient equals
the separate effective forms plus the genuine Laplace transform of the kernel. -/
theorem effectiveForm_addSMul_laplace {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {s : ℝ} (hs : 0 < s) (e f : Symmetric d) :
    effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le)) e f =
      effectiveForm V e f + s⁻¹ * effectiveForm E e f +
        ⟪e, action (halfLineLaplace C.kernel s) f⟫_ℝ := by
  sorry

end KVApproximation.Homogenization
