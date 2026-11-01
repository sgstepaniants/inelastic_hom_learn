module

public import KVApproximation.Analysis.CutoffPairing
public import KVApproximation.Analysis.VectorSobolevFields

public section

open MeasureTheory TopologicalSpace
open KVApproximation.Tensor
open scoped Distributions Gradient InnerProductSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, localized test gradients: the bounded L² map has the
physical-coordinate outer-product representative. -/
theorem cutoffGradientL_apply_ae (χ : 𝓓(Ω, ℝ))
    (u : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    cutoffGradientL χ u =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      WithLp.toLp 2 (fun ij => u x ij.1 * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2) := by
  sorry

/-- Theorem 3.1, localized flux limits: the continuous bilinear form
is the integral of the physical stress, displacement and cutoff gradient. -/
theorem cutoffPairing_eq_integral (χ : 𝓓(Ω, ℝ))
    (σ : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (u : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d)))) :
    cutoffPairing χ σ u = ∫ x in (Ω : Set (PhysicalSpace d)),
      ∑ ij : Fin d × Fin d, (σ x).val ij * u x ij.1 *
        (∇ (χ : PhysicalSpace d → ℝ) x) ij.2 := by
  sorry

/-- Theorem 3.1, localized weak tests: the full-gradient product rule
splits the stress pairing into the localized strain and cutoff terms. -/
theorem integral_stress_cutoff_gradient (χ : 𝓓(Ω, ℝ))
    (σ : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (u : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (G : Lp (SecondOrder d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (v : VectorH1 Ω)
    (hv : VectorH1.gradientL Ω v =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x =>
      WithLp.toLp 2 (fun ij => χ x * G x ij +
        u x ij.1 * (∇ (χ : PhysicalSpace d → ℝ) x) ij.2)) :
    (∫ x in (Ω : Set (PhysicalSpace d)), ⟪σ x, VectorH1.symmetricGradientL Ω v x⟫_ℝ) =
      (∫ x in (Ω : Set (PhysicalSpace d)), χ x * ⟪(σ x).val, G x⟫_ℝ) +
        cutoffPairing χ σ u := by
  sorry

/-- Theorem 3.1, localized divergence-free stresses: testing with χu
expresses the strain pairing using only the displacement value. -/
theorem integral_cutoff_stress_strain_eq_neg_pairing (χ : 𝓓(Ω, ℝ))
    (σ : Lp (Symmetric d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (hσ : ∀ v : ZeroBoundaryH1 Ω,
      (∫ x in (Ω : Set (PhysicalSpace d)), ⟪σ x, VectorH1.symmetricGradientL Ω v.val x⟫_ℝ) = 0)
    (u : ZeroBoundaryH1 Ω) :
    (∫ x in (Ω : Set (PhysicalSpace d)),
      χ x * ⟪σ x, VectorH1.symmetricGradientL Ω u.val x⟫_ℝ) =
        -cutoffPairing χ σ (VectorH1.valueL Ω u.val) := by
  sorry

end KVApproximation.Analysis
