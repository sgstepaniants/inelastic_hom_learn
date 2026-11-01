module

public import KVApproximation.Analysis.PeriodicCell

/-!
# Continuous linear Fourier coefficients
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Example 2.1 and Remark 4.3, Fourier ingredient: every coordinate Fourier
coefficient is a continuous real-linear functional on the actual Euclidean L² space. -/
theorem exists_periodicFourierCoefficientCLM
    {d : ℕ} {ι : Type*} [Fintype ι] (k : Fin d → ℤ) (j : ι) :
    ∃ A : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d) →L[ℝ] ℂ,
      ∀ f : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d),
        A f = ∫ y, UnitAddTorus.mFourier (-k) y * (f y j : ℂ) ∂cellMeasure d := by
  let C : EuclideanSpace ℝ ι →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : ι => ℝ) j)
  let A : Lp ℂ 2 (cellMeasure d) →L[ℝ] ℂ :=
    (innerSL ℂ (UnitAddTorus.mFourierLp 2 k)).restrictScalars ℝ
  refine ⟨A.comp (C.compLpL 2 (cellMeasure d)), ?_⟩
  intro f
  change ⟪UnitAddTorus.mFourierLp 2 k, C.compLpL 2 (cellMeasure d) f⟫_ℂ = _
  calc
    _ = ⟪UnitAddTorus.mFourierBasis k, C.compLpL 2 (cellMeasure d) f⟫_ℂ :=
      congrArg (fun q : Lp ℂ 2 (cellMeasure d) =>
        ⟪q, C.compLpL 2 (cellMeasure d) f⟫_ℂ)
        (congrFun (UnitAddTorus.coe_mFourierBasis (d := Fin d)) k).symm
    _ = UnitAddTorus.mFourierBasis.repr (C.compLpL 2 (cellMeasure d) f) k :=
      (UnitAddTorus.mFourierBasis.repr_apply_apply (C.compLpL 2 (cellMeasure d) f) k).symm
    _ = UnitAddTorus.mFourierCoeff (C.compLpL 2 (cellMeasure d) f) k :=
      UnitAddTorus.mFourierBasis_repr (C.compLpL 2 (cellMeasure d) f) k
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [C.coeFn_compLpL f] with y hy
      change UnitAddTorus.mFourier (-k) y * (C.compLpL 2 (cellMeasure d) f) y = _
      rw [hy]
      rfl

/-- Remark 4.3, separation of function inputs: all coordinate Fourier
coefficients determine the actual Euclidean L² field on the normalized cell. -/
theorem euclideanL2_eq_of_fourier_integrals_eq
    {d : ℕ} {ι : Type*} [Fintype ι]
    {f g : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d)}
    (h : ∀ k : Fin d → ℤ, ∀ j : ι,
      (∫ y, UnitAddTorus.mFourier (-k) y * (f y j : ℂ) ∂cellMeasure d) =
        ∫ y, UnitAddTorus.mFourier (-k) y * (g y j : ℂ) ∂cellMeasure d) :
    f = g := by
  have hcoordinate (j : ι) : ∀ᵐ y ∂cellMeasure d, (f y j : ℂ) = (g y j : ℂ) := by
    let C : EuclideanSpace ℝ ι →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : ι => ℝ) j)
    let b : HilbertBasis (Fin d → ℤ) ℂ (Lp ℂ 2 (cellMeasure d)) :=
      UnitAddTorus.mFourierBasis
    have hLp : C.compLpL 2 (cellMeasure d) f = C.compLpL 2 (cellMeasure d) g := by
      apply b.repr.injective
      apply lp.ext
      funext k
      change UnitAddTorus.mFourierBasis.repr (C.compLpL 2 (cellMeasure d) f) k =
        UnitAddTorus.mFourierBasis.repr (C.compLpL 2 (cellMeasure d) g) k
      have hf : UnitAddTorus.mFourierCoeff (C.compLpL 2 (cellMeasure d) f) k =
          ∫ y, UnitAddTorus.mFourier (-k) y * (f y j : ℂ) ∂cellMeasure d := by
        apply integral_congr_ae
        filter_upwards [C.coeFn_compLpL f] with y hy
        change UnitAddTorus.mFourier (-k) y * (C.compLpL 2 (cellMeasure d) f) y = _
        rw [hy]
        rfl
      have hg : UnitAddTorus.mFourierCoeff (C.compLpL 2 (cellMeasure d) g) k =
          ∫ y, UnitAddTorus.mFourier (-k) y * (g y j : ℂ) ∂cellMeasure d := by
        apply integral_congr_ae
        filter_upwards [C.coeFn_compLpL g] with y hy
        change UnitAddTorus.mFourier (-k) y * (C.compLpL 2 (cellMeasure d) g) y = _
        rw [hy]
        rfl
      exact (UnitAddTorus.mFourierBasis_repr (C.compLpL 2 (cellMeasure d) f) k).trans
        (hf.trans ((h k j).trans (hg.symm.trans
          (UnitAddTorus.mFourierBasis_repr (C.compLpL 2 (cellMeasure d) g) k).symm)))
    filter_upwards [C.coeFn_compLpL f, C.coeFn_compLpL g] with y hf hg
    change C (f y) = C (g y)
    rw [← hf, ← hg, hLp]
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoordinate] with y hy
  apply PiLp.ext
  intro j
  exact Complex.ofReal_injective (hy j)

end KVApproximation.Analysis
