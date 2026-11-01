module

public import KVApproximation.Spectral.StrongAdditivity
public import KVApproximation.Spectral.TensorVariation
public import KVApproximation.Analysis.VectorMeasureIntegral

/-!
# Finite-dimensional compression of a projection-valued measure

Real parts of the compressed spectral pairings define symmetric bilinear forms.
Their tensor representatives are countably additive because every scalar pairing
is countably additive and the tensor space is finite-dimensional.
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance pvmCompressionRealInnerProduct : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

omit [CompleteSpace H] in
/-- Appendix A.2: the real part of the complex inner product is symmetric. -/
private theorem re_inner_swap (u v : H) : (⟪u, v⟫_ℂ).re = (⟪v, u⟫_ℂ).re := by
  simpa only [RCLike.re_eq_complex_re] using inner_re_symm (𝕜 := ℂ) u v

/-- Appendix A.2: the real bilinear compression of a spectral projection. -/
private def projectedForm {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) (B : Set ℝ) (hB : MeasurableSet B) :
    Symmetric d →L[ℝ] Symmetric d →L[ℝ] ℝ :=
  (innerSL ℝ (E := H)).bilinearComp (((P.proj B hB).restrictScalars ℝ).comp L) L

/-- Appendix A.2: self-adjointness of the projection gives symmetry over the reals. -/
private theorem projectedForm_symmetric {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) (B : Set ℝ) (hB : MeasurableSet B)
    (e f : Symmetric d) : projectedForm P L B hB e f = projectedForm P L B hB f e := by
  change (⟪P.proj B hB (L e), L f⟫_ℂ).re = (⟪P.proj B hB (L f), L e⟫_ℂ).re
  calc
    _ = (⟪L e, P.proj B hB (L f)⟫_ℂ).re := congrArg Complex.re
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (P.isSelfAdjoint_proj B hB))
        (L e) (L f))
    _ = _ := re_inner_swap _ _

/-- Appendix A.2: the unique tensor on measurable sets, and zero elsewhere. -/
private def projectedTensor {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) (B : Set ℝ) : Elasticity d := by
  classical
  exact if hB : MeasurableSet B then
    (existsUnique_form_tensor (projectedForm P L B hB) (projectedForm_symmetric P L B hB)).choose
  else 0

/-- Appendix A.2 (`eq:nu_def`): the selected tensor represents the prescribed pairing. -/
private theorem projectedTensor_spec {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) (B : Set ℝ) (hB : MeasurableSet B) (e f : Symmetric d) :
    ⟪e, action (projectedTensor P L B) f⟫_ℝ = (⟪P.proj B hB (L e), L f⟫_ℂ).re := by
  unfold projectedTensor
  rw [dite_eq_left hB]
  exact (existsUnique_form_tensor (projectedForm P L B hB)
    (projectedForm_symmetric P L B hB)).choose_spec.1 e f

/-- Appendix A.2: strong additivity passes through every compressed scalar pairing. -/
private def projectedMeasure {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) : TensorMeasure d where
  measureOf' := projectedTensor P L
  empty' := by
    apply eq_of_inner_action_eq
    intro e f
    rw [projectedTensor_spec P L ∅ MeasurableSet.empty, P.proj_empty]
    change (⟪(0 : H), L f⟫_ℂ).re = ⟪e, (actionL d 0) f⟫_ℝ
    simp
  not_measurable' B hB := by simp only [projectedTensor, dite_eq_right hB]
  m_iUnion' s hs hd := by
    apply hasSum_of_inner_action
    intro e f
    let φ : H →L[ℝ] ℝ := innerSL ℝ (L f)
    have h := (projectionMeasure_hasSum P s hs hd (L e)).mapL φ
    convert h using 1
    · funext n
      rw [projectedTensor_spec P L (s n) (hs n)]
      change (⟪P.proj (s n) (hs n) (L e), L f⟫_ℂ).re =
        (⟪L f, P.proj (s n) (hs n) (L e)⟫_ℂ).re
      exact re_inner_swap _ _
    · rw [projectedTensor_spec P L (⋃ n, s n) (MeasurableSet.iUnion hs)]
      change (⟪P.proj (⋃ n, s n) (MeasurableSet.iUnion hs) (L e), L f⟫_ℂ).re =
        (⟪L f, P.proj (⋃ n, s n) (MeasurableSet.iUnion hs) (L e)⟫_ℂ).re
      exact re_inner_swap _ _

/-- Appendix A.2 (`eq:nu_def`): finite-dimensional compression of a general PVM
is a unique countably additive tensor measure. -/
theorem pvmCompression_exists_unique {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) :
    ∃! ν : TensorMeasure d, ∀ (B : Set ℝ) (hB : MeasurableSet B) (e f : Symmetric d),
      ⟪e, action (ν B) f⟫_ℝ = (⟪P.proj B hB (L e), L f⟫_ℂ).re := by
  refine ⟨projectedMeasure P L, projectedTensor_spec P L, ?_⟩
  intro ν hν
  apply VectorMeasure.ext
  intro B hB
  apply eq_of_inner_action_eq
  intro e f
  exact (hν B hB e f).trans (projectedTensor_spec P L B hB e f).symm

/-- Appendix A.2: the compressed PVM is positive; its total trace and
Frobenius variation are controlled by the compression energies. -/
theorem pvmCompression_positive_trace {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d →L[ℝ] H) (ν : TensorMeasure d)
    (hν : ∀ (B : Set ℝ) (hB : MeasurableSet B) (e f : Symmetric d),
      ⟪e, action (ν B) f⟫_ℝ = (⟪P.proj B hB (L e), L f⟫_ℂ).re)
    {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ (Symmetric d)) :
    ν.Positive ∧ tensorTrace (ν Set.univ) = ∑ i, ‖L (b i)‖ ^ 2 ∧
      totalVariation ν Set.univ ≤ ENNReal.ofReal (∑ i, ‖L (b i)‖ ^ 2) := by
  have hpos : ν.Positive := by
    intro B hB e
    rw [hν B hB e e, re_inner_swap, P.inner_proj]
    exact ENNReal.toReal_nonneg
  have htrace : tensorTrace (ν Set.univ) = ∑ i, ‖L (b i)‖ ^ 2 := by
    rw [tensorTrace_eq_sum b]
    apply Finset.sum_congr rfl
    intro i _
    rw [hν Set.univ MeasurableSet.univ, P.proj_univ, ContinuousLinearMap.id_apply]
    simpa only [RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) (L (b i))).symm
  refine ⟨hpos, htrace, ?_⟩
  rw [← htrace]
  exact ν.variation_le_trace hpos MeasurableSet.univ

/-- Appendix A.2: integrable diagonal tensor tests equal the positive scalar
spectral integral. Mixed tests are recovered by real polarization. -/
theorem pvmCompression_integral_diag {d : ℕ} (P : TauCeti.ProjValMeasure H)
    (L : Symmetric d → H) (ν : TensorMeasure d)
    (hν : ∀ (B : Set ℝ) (hB : MeasurableSet B) (e g : Symmetric d),
      ⟪e, action (ν B) g⟫_ℝ = (⟪P.proj B hB (L e), L g⟫_ℂ).re)
    (f : ℝ → ℝ) (e : Symmetric d)
    (hνf : Integrable f ν.variation) (hPf : Integrable f (P.diag (L e))) :
    ⟪e, action (tensorIntegral ν f) e⟫_ℝ = ∫ r, f r ∂P.diag (L e) := by
  let φ : Elasticity d →L[ℝ] ℝ := (innerSL ℝ e).comp ((actionL d).flip e)
  have hφ : ∀ B : Set ℝ, MeasurableSet B → φ (ν B) = (P.diag (L e)).real B := by
    intro B hB
    change ⟪e, action (ν B) e⟫_ℝ = (P.diag (L e) B).toReal
    rw [hν B hB, re_inner_swap, P.inner_proj, Complex.ofReal_re]
  exact Analysis.integral_scalarization ν φ (P.diag (L e)) hφ f hνf hPf

end KVApproximation.Spectral
