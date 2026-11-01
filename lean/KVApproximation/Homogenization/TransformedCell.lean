module

public import KVApproximation.Homogenization.CellConstitutive
public import KVApproximation.Tensor.FieldCombinations
public import KVApproximation.OperatorTheory.CellResolvent
public import KVApproximation.OperatorTheory.CfcLaplace
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# The transformed periodic cell equation
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Theorem 3.1, transformed cell equation: a positive upper majorant
also covers zero-dimensional strain spaces, whose recorded upper bound
need not be positive. The coefficient and its lower bound are unchanged. -/
private theorem positive_fieldForm_bounds {d : ℕ} (A : CoerciveField d) :
    A.toForm.HasBounds A.lower (max A.upper A.lower) := by
  intro u
  have hu := A.bounds u
  have hupper : fieldPairing A.field u u ≤ max A.upper A.lower * ‖u‖ ^ 2 :=
    hu.2.trans (mul_le_mul_of_nonneg_right (le_max_left A.upper A.lower) (sq_nonneg ‖u‖))
  simpa only [CoerciveField.toForm, boundedFieldForm_apply] using And.intro hu.1 hupper

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
  let A := V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le)
  have hA (u v : StrainField d) :
      A.toForm.form u v = V.toForm.form u v + s⁻¹ * E.toForm.form u v := by
    simpa only [A, CoerciveField.toForm, CoerciveField.addSMul, boundedFieldForm_apply] using
      fieldPairing_add_smul V.field E.field s⁻¹ u v
  have h := homogenizedForm_resolvent V.toForm E.toForm A.toForm
    (correctorSubspace d) (constantStrainL d) s hs hA
    V.lower_pos (V.lower_pos.trans_le (le_max_right V.upper V.lower))
    E.lower_pos (E.lower_pos.trans_le (le_max_right E.upper E.lower))
    (positive_fieldForm_bounds V) (positive_fieldForm_bounds E) e f
  change _ = effectiveForm A e f - effectiveForm V e f - s⁻¹ * effectiveForm E e f at h
  linarith

/-- Theorem 3.1, transform of the cell kernel: coercivity places the
actual weighted relaxation spectrum in the nonnegative real axis. -/
private theorem cell_relaxation_spectrum_nonneg {d : ℕ} (V E : CoerciveField d) :
    ∀ r ∈ spectrum ℝ (weightedRelaxation V.toForm E.toForm (correctorSubspace d)),
      0 ≤ r := by
  have hβ : 0 < max V.upper V.lower :=
    V.lower_pos.trans_le (le_max_right V.upper V.lower)
  have hbound := weightedRelaxation_lower_bound V.toForm E.toForm (correctorSubspace d)
    hβ E.lower_pos (positive_fieldForm_bounds V) (positive_fieldForm_bounds E)
  have hs := (algebraMap_le_iff_le_spectrum
    (weightedRelaxation_isSelfAdjoint V.toForm E.toForm (correctorSubspace d))).mp hbound
  exact fun r hr => (div_pos E.lower_pos hβ).le.trans (hs r hr)

/-- Theorem 3.1 and Appendix A.2: the memory form is the compression
of the spectral multiplier r exp(-tr), before choosing a periodic cell space. -/
private theorem memoryForm_cfc {H F : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H)
    (t : ℝ) (e f : F) :
    memoryForm V E X ι t e f =
      ⟪cfc (fun r : ℝ => r * Real.exp (-r * t)) (weightedRelaxation V E X)
        (weightedMismatch V E X ι e), weightedMismatch V E X ι f⟫_ℝ := by
  symm
  have hR := weightedRelaxation_isSelfAdjoint V E X
  have hf : (fun r : ℝ => Real.exp (-r * t)) =
      (fun r : ℝ => Real.exp (-t * r)) := by
    funext r
    congr 1
    ring
  rw [cfc_mul _ _ _ (by fun_prop) (by fun_prop), cfc_id' ℝ _ hR, hf,
    cfc_comp_const_mul _ Real.exp _ Real.continuous_exp.continuousOn hR,
    CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all _).smul hR),
    ← relaxationSemigroup_conjugate V E X t]
  let W := (WeightedSpace.continuousLinearEquiv
    (V.restrict X)).symm.conjContinuousAlgEquiv
  change ⟪(W (relaxation V E X) *
      W (relaxationSemigroup V E X t))
    (weightedMismatch V E X ι e),
    weightedMismatch V E X ι f⟫_ℝ = _
  rw [← map_mul]
  rfl

/-- Theorem 3.1, transformed memory: integrate the generic compressed
operator before substituting the periodic strain-corrector space. -/
private theorem memoryForm_laplace {H F : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H)
    (hpos : ∀ r ∈ spectrum ℝ (weightedRelaxation V E X), 0 ≤ r)
    {s : ℝ} (hs : 0 < s) (e f : F) :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * t) * memoryForm V E X ι t e f) =
      ⟪cfc (fun r : ℝ => r / (s + r)) (weightedRelaxation V E X)
        (weightedMismatch V E X ι e), weightedMismatch V E X ι f⟫_ℝ := by
  let R := weightedRelaxation V E X
  let D := weightedMismatch V E X ι
  let L : (RelaxationSpace V X →L[ℝ] RelaxationSpace V X) →L[ℝ] ℝ :=
    (innerSL ℝ (D f)).comp (ContinuousLinearMap.apply ℝ _ (D e))
  have hR := weightedRelaxation_isSelfAdjoint V E X
  have hint := integrable_cfc_memory_laplace R hR hpos hs
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ),
        L (Real.exp (-s * t) • cfc (fun r : ℝ => r * Real.exp (-r * t)) R) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        change Real.exp (-s * t) * memoryForm V E X ι t e f =
          L (Real.exp (-s * t) • cfc (fun r : ℝ => r * Real.exp (-r * t)) R)
        rw [map_smul]
        change Real.exp (-s * t) * memoryForm V E X ι t e f =
          Real.exp (-s * t) * ⟪D f, cfc (fun r : ℝ => r * Real.exp (-r * t)) R (D e)⟫_ℝ
        exact congrArg (Real.exp (-s * t) * ·)
          ((memoryForm_cfc V E X ι t e f).trans (real_inner_comm _ _))
    _ = L (halfLineLaplace (fun t : ℝ =>
        cfc (fun r : ℝ => r * Real.exp (-r * t)) R) s) := L.integral_comp_comm hint
    _ = _ := by
      rw [halfLineLaplace_cfc_memory R hR hpos hs]
      exact (real_inner_comm (D f) (cfc (fun r : ℝ => r / (s + r)) R (D e))).symm

/-- Theorem 3.1 and Appendix A.2: specialization to the actual
periodic strain-corrector space and its constant-strain embedding. -/
private theorem cellMemoryForm_cfc {d : ℕ} (V E : CoerciveField d)
    (t : ℝ) (e f : Symmetric d) :
    cellMemoryForm V E t e f =
      ⟪cfc (fun r : ℝ => r * Real.exp (-r * t))
        (weightedRelaxation V.toForm E.toForm (correctorSubspace d))
        (weightedMismatch V.toForm E.toForm (correctorSubspace d) (constantStrainL d) e),
        weightedMismatch V.toForm E.toForm (correctorSubspace d) (constantStrainL d) f⟫_ℝ :=
  memoryForm_cfc V.toForm E.toForm (correctorSubspace d) (constantStrainL d) t e f

/-- Theorem 3.1, transform of the cell kernel: each weighted tensor
pairing is an integrable continuous-linear image of the operator integrand. -/
private theorem cellKernel_pairing_integrable {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {s : ℝ} (hs : 0 < s) (e f : Symmetric d) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) * ⟪e, action (C.kernel t) f⟫_ℝ)
      (Set.Ioi (0 : ℝ)) := by
  let R := weightedRelaxation V.toForm E.toForm (correctorSubspace d)
  let D := weightedMismatch V.toForm E.toForm (correctorSubspace d) (constantStrainL d)
  let L : (RelaxationSpace V.toForm (correctorSubspace d) →L[ℝ]
      RelaxationSpace V.toForm (correctorSubspace d)) →L[ℝ] ℝ :=
    (innerSL ℝ (D f)).comp (ContinuousLinearMap.apply ℝ _ (D e))
  have hint := integrable_cfc_memory_laplace R
    (weightedRelaxation_isSelfAdjoint V.toForm E.toForm (correctorSubspace d))
    (cell_relaxation_spectrum_nonneg V E) hs
  have h := L.integrable_comp hint
  apply h.congr
  exact Filter.Eventually.of_forall fun t => by
    change L (Real.exp (-s * t) • cfc (fun r : ℝ => r * Real.exp (-r * t)) R) =
      Real.exp (-s * t) * ⟪e, action (C.kernel t) f⟫_ℝ
    rw [map_smul]
    change Real.exp (-s * t) * ⟪D f, cfc (fun r : ℝ => r * Real.exp (-r * t)) R (D e)⟫_ℝ = _
    apply congrArg (Real.exp (-s * t) * ·)
    exact (real_inner_comm _ _).trans
      ((C.kernel_eq t e f).trans (cellMemoryForm_cfc V E t e f)).symm

/-- Theorem 3.1, Laplace transform of the memory kernel: the actual
tensor-valued cell kernel is Bochner integrable against every positive-rate
exponential on the whole positive time axis. -/
theorem cellKernel_integrable_halfLineLaplace {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) • C.kernel t) (Set.Ioi (0 : ℝ)) := by
  classical
  let b := stdOrthonormalBasis ℝ (Symmetric d)
  have htrace : IntegrableOn (fun t : ℝ => Real.exp (-s * t) * tensorTrace (C.kernel t))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrable_finsetSum Finset.univ
      (fun i _ => cellKernel_pairing_integrable V E C hs (b i) (b i))
    apply h.congr
    exact Filter.Eventually.of_forall fun t => by
      dsimp only
      rw [tensorTrace_eq_sum b, Finset.mul_sum]
  have hcont : Continuous (fun t : ℝ => Real.exp (-s * t) • C.kernel t) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-s * t))).smul
      (cellKernel_continuous V E C)
  apply htrace.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (norm_le_tensorTrace (C.kernel t) (cellKernel_nonneg V E C t ht.le)) (Real.exp_pos _).le

/-- Theorem 3.1, constitutive identification in the proof following
`eq:homogenized_model_identified`: the effective combined coefficient equals
the separate effective forms plus the genuine Laplace transform of the kernel. -/
theorem effectiveForm_addSMul_laplace {d : ℕ} (V E : CoerciveField d)
    (C : CellConstitutiveModel V E) {s : ℝ} (hs : 0 < s) (e f : Symmetric d) :
    effectiveForm (V.addSMul E s⁻¹ (inv_nonneg.mpr hs.le)) e f =
      effectiveForm V e f + s⁻¹ * effectiveForm E e f +
        ⟪e, action (halfLineLaplace C.kernel s) f⟫_ℝ := by
  let Q : Elasticity d →L[ℝ] ℝ := (innerSL ℝ e).comp ((actionL d).flip f)
  have hQ : ⟪e, action (halfLineLaplace C.kernel s) f⟫_ℝ =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-s * t) * cellMemoryForm V E t e f := by
    calc
      _ = ∫ t in Set.Ioi (0 : ℝ), Q (Real.exp (-s * t) • C.kernel t) :=
        (Q.integral_comp_comm (cellKernel_integrable_halfLineLaplace V E C hs)).symm
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by
          change Q (Real.exp (-s * t) • C.kernel t) =
            Real.exp (-s * t) * cellMemoryForm V E t e f
          rw [map_smul]
          exact congrArg (Real.exp (-s * t) * ·) (C.kernel_eq t e f)
  have hLap := memoryForm_laplace V.toForm E.toForm (correctorSubspace d) (constantStrainL d)
    (cell_relaxation_spectrum_nonneg V E) hs e f
  exact (effectiveForm_addSMul_resolvent V E hs e f).trans
    (congrArg (effectiveForm V e f + s⁻¹ * effectiveForm E e f + ·) (hQ.trans hLap).symm)

end KVApproximation.Homogenization
