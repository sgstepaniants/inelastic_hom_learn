module

public import KVApproximation.Analysis.PeriodicFourier
public import KVApproximation.Analysis.PeriodicComplexTests

/-!
# Fourier coefficients of periodic weak derivatives
-/

public section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Section 3.1, periodic Sobolev foundations: the Fourier coefficients of
the weak gradient are frequency multiples of those of the displacement. -/
theorem HasPeriodicWeakGradient.fourier_coefficient {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g : Lp (SecondOrder d) 2 (cellMeasure d)}
    (h : HasPeriodicWeakGradient u g) (n : Fin d → ℤ) (i j : Fin d) :
    (∫ y, UnitAddTorus.mFourier (-n) y * (g y (i, j) : ℂ) ∂cellMeasure d) =
      (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
        ∫ y, UnitAddTorus.mFourier (-n) y * (u y i : ℂ) ∂cellMeasure d := by
  let φ : PeriodicC1 d ℂ :=
    ⟨UnitAddTorus.mFourier (-n), (contDiff_mFourier_lift (-n)).of_le (by simp)⟩
  let k : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)
  have hp (y : PeriodicCell d) :
      φ.partial j y = -k * UnitAddTorus.mFourier (-n) y := by
    have hd := fderiv_mFourier_lift_apply (-n) (cellRepresentative y) j
    simpa only [φ, PeriodicC1.partial, k, toCell_cellRepresentative,
      Pi.neg_apply, Int.cast_neg, mul_neg] using hd
  have hparts := h.integral_complex_test φ i j
  have hleft : (fun y => u y i • φ.partial j y) =
      fun y => -k * (UnitAddTorus.mFourier (-n) y * (u y i : ℂ)) := by
    funext y
    rw [hp, Complex.real_smul]
    ring
  have hright : (fun y => g y (i, j) • φ.value y) =
      fun y => UnitAddTorus.mFourier (-n) y * (g y (i, j) : ℂ) := by
    funext y
    rw [Complex.real_smul]
    exact mul_comm _ _
  rw [hleft, hright, integral_const_mul, neg_mul] at hparts
  exact (neg_inj.mp hparts).symm

/-- Section 3.1, periodic Sobolev foundations: all Fourier coefficients
determine a complex L² field on the normalized unit torus. -/
theorem eq_of_fourier_integrals_eq {d : ℕ}
    {f g : Lp ℂ 2 (cellMeasure d)}
    (h : ∀ n : Fin d → ℤ,
      (∫ y, UnitAddTorus.mFourier (-n) y * f y ∂cellMeasure d) =
        ∫ y, UnitAddTorus.mFourier (-n) y * g y ∂cellMeasure d) : f = g := by
  -- Mathlib's torus basis uses exactly the normalized product Haar measure.
  let b : HilbertBasis (Fin d → ℤ) ℂ (Lp ℂ 2 (cellMeasure d)) :=
    UnitAddTorus.mFourierBasis
  apply b.repr.injective
  apply lp.ext
  funext n
  change UnitAddTorus.mFourierBasis.repr f n = UnitAddTorus.mFourierBasis.repr g n
  exact (UnitAddTorus.mFourierBasis_repr f n).trans
    ((h n).trans (UnitAddTorus.mFourierBasis_repr g n).symm)

/-- Section 3.1: the periodic distributional gradient is unique. -/
theorem HasPeriodicWeakGradient.gradient_unique {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g₁ g₂ : Lp (SecondOrder d) 2 (cellMeasure d)}
    (h₁ : HasPeriodicWeakGradient u g₁) (h₂ : HasPeriodicWeakGradient u g₂) :
    g₁ = g₂ := by
  have hcoord (ij : Fin d × Fin d) :
      ∀ᵐ y ∂cellMeasure d, (g₁ y ij : ℂ) = (g₂ y ij : ℂ) := by
    let L : SecondOrder d →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d × Fin d => ℝ) ij)
    have hLp : L.compLpL 2 (cellMeasure d) g₁ = L.compLpL 2 (cellMeasure d) g₂ := by
      apply eq_of_fourier_integrals_eq
      intro n
      have hleft : (∫ y, UnitAddTorus.mFourier (-n) y *
          (L.compLpL 2 (cellMeasure d) g₁) y ∂cellMeasure d) =
            ∫ y, UnitAddTorus.mFourier (-n) y * (g₁ y ij : ℂ) ∂cellMeasure d := by
        apply integral_congr_ae
        filter_upwards [L.coeFn_compLpL g₁] with y hy
        rw [hy]
        rfl
      have hright : (∫ y, UnitAddTorus.mFourier (-n) y *
          (L.compLpL 2 (cellMeasure d) g₂) y ∂cellMeasure d) =
            ∫ y, UnitAddTorus.mFourier (-n) y * (g₂ y ij : ℂ) ∂cellMeasure d := by
        apply integral_congr_ae
        filter_upwards [L.coeFn_compLpL g₂] with y hy
        rw [hy]
        rfl
      rw [hleft, hright, h₁.fourier_coefficient n ij.1 ij.2,
        h₂.fourier_coefficient n ij.1 ij.2]
    filter_upwards [L.coeFn_compLpL g₁, L.coeFn_compLpL g₂] with y hleft hright
    change L (g₁ y) = L (g₂ y)
    rw [← hleft, ← hright, hLp]
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord] with y hy
  apply PiLp.ext
  intro ij
  exact Complex.ofReal_injective (hy ij)

end KVApproximation.Analysis
