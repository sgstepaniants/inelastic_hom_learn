module

public import KVApproximation.Analysis.CompactLaplaceUniqueness
public import KVApproximation.Analysis.PositiveScalarization
public import KVApproximation.Spectral.TensorMeasureIntegration
public import KVApproximation.Tensor.FormRepresentation
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Uniqueness of the tensor spectral representation
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Spectral

/-- Proposition 3.3, uniqueness of its measure on a positive compact interval.
Diagonal scalar measures are determined by the kernel at integer times;
real polarization recovers the complete tensor measure. -/
theorem spectral_representation_unique {d : ℕ} {lower upper : ℝ}
    (hlower : 0 < lower) (ν₁ ν₂ : TensorMeasure d) (K : ℝ → Elasticity d)
    (hν₁ : IsSpectralRepresentation ν₁ K lower upper)
    (hν₂ : IsSpectralRepresentation ν₂ K lower upper) : ν₁ = ν₂ := by
  have hdiag (e : Symmetric d) (s : Set ℝ) (hs : MeasurableSet s) :
      ⟪e, action (ν₁ s) e⟫_ℝ = ⟪e, action (ν₂ s) e⟫_ℝ := by
    let φ : Elasticity d →L[ℝ] ℝ := (innerSL ℝ e).comp ((actionL d).flip e)
    obtain ⟨μ₁, hfinite₁, hreal₁, hnull₁⟩ :=
      exists_finite_positive_scalarization ν₁ φ (fun B hB => hν₁.1 B hB e)
    obtain ⟨μ₂, hfinite₂, hreal₂, hnull₂⟩ :=
      exists_finite_positive_scalarization ν₂ φ (fun B hB => hν₂.1 B hB e)
    let := hfinite₁
    let := hfinite₂
    have hsupp₁ : μ₁ (Set.Icc lower upper)ᶜ = 0 :=
      hnull₁ _ measurableSet_Icc.compl hν₁.2.1
    have hsupp₂ : μ₂ (Set.Icc lower upper)ᶜ = 0 :=
      hnull₂ _ measurableSet_Icc.compl hν₂.2.1
    have hμeq : μ₁ = μ₂ := by
      apply measure_eq_of_weighted_exponential_moments hlower μ₁ μ₂ hsupp₁ hsupp₂
      intro n
      let f : ℝ → ℝ := fun r => r * Real.exp (-r * n)
      have hf : Continuous f := by dsimp [f]; fun_prop
      have hfi₁ : Integrable f μ₁ := by
        have hi := hf.continuousOn.integrableOn_Icc (μ := μ₁) (a := lower) (b := upper)
        rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp₁)] at hi
      have hfi₂ : Integrable f μ₂ := by
        have hi := hf.continuousOn.integrableOn_Icc (μ := μ₂) (a := lower) (b := upper)
        rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp₂)] at hi
      have h₁ := integral_scalarization ν₁ φ μ₁ (fun B hB => (hreal₁ B hB).symm)
        f (ν₁.integrable_continuousOn hν₁.2.2.1 hν₁.2.1 f hf.continuousOn) hfi₁
      have h₂ := integral_scalarization ν₂ φ μ₂ (fun B hB => (hreal₂ B hB).symm)
        f (ν₂.integrable_continuousOn hν₂.2.2.1 hν₂.2.1 f hf.continuousOn) hfi₂
      have hkernel : tensorIntegral ν₁ f = tensorIntegral ν₂ f :=
        (hν₁.2.2.2 n (Nat.cast_nonneg n)).symm.trans (hν₂.2.2.2 n (Nat.cast_nonneg n))
      have heq : (∫ r, f r ∂μ₁) = ∫ r, f r ∂μ₂ :=
        h₁.symm.trans ((congrArg φ hkernel).trans h₂)
      have hfexp : f = fun r => r * Real.exp (-r) ^ n := by
        funext r
        dsimp [f]
        rw [mul_comm (-r), Real.exp_nat_mul]
      simpa only [hfexp] using heq
    change φ (ν₁ s) = φ (ν₂ s)
    rw [← hreal₁ s hs, ← hreal₂ s hs, hμeq]
  apply VectorMeasure.ext
  intro s hs
  let B (ν : TensorMeasure d) : LinearMap.BilinForm ℝ (Symmetric d) :=
    ((innerSL ℝ).comp (actionL d (ν s))).toLinearMap₁₂
  have hsymm (ν : TensorMeasure d) : (B ν).IsSymm := ⟨fun e g => by
    change ⟪action (ν s) e, g⟫_ℝ = ⟪action (ν s) g, e⟫_ℝ
    rw [action_symmetric, real_inner_comm]⟩
  have hB : B ν₁ = B ν₂ :=
    LinearMap.BilinForm.ext_of_isSymm (hsymm ν₁) (hsymm ν₂) fun e => by
      change ⟪action (ν₁ s) e, e⟫_ℝ = ⟪action (ν₂ s) e, e⟫_ℝ
      simpa only [action_symmetric] using hdiag e s hs
  apply eq_of_inner_action_eq
  intro e g
  have heq := congrArg (fun Q : LinearMap.BilinForm ℝ (Symmetric d) => Q e g) hB
  change ⟪action (ν₁ s) e, g⟫_ℝ = ⟪action (ν₂ s) e, g⟫_ℝ at heq
  simpa only [action_symmetric] using heq

end KVApproximation.Spectral
