module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Parseval's identity for periodic Euclidean fields
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Section 3.1, periodic Sobolev foundations: Parseval's identity with
all Euclidean coordinates and the normalized torus measure. -/
theorem hasSum_fourier_energy {d : ℕ} {ι : Type*} [Fintype ι]
    (f : Lp (EuclideanSpace ℝ ι) 2 (cellMeasure d)) :
    HasSum (fun n : Fin d → ℤ => ∑ i,
      ‖∫ y, UnitAddTorus.mFourier (-n) y * (f y i : ℂ) ∂cellMeasure d‖ ^ 2)
      (‖f‖ ^ 2) := by
  have hscalar (i : ι) :
      HasSum (fun n : Fin d → ℤ =>
        ‖∫ y, UnitAddTorus.mFourier (-n) y * (f y i : ℂ) ∂cellMeasure d‖ ^ 2)
        (∫ y, (f y i) ^ 2 ∂cellMeasure d) := by
    let L : EuclideanSpace ℝ ι →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : ι => ℝ) i)
    let F : Lp ℂ 2 (cellMeasure d) := L.compLpL 2 (cellMeasure d) f
    have hsum : HasSum (fun n : Fin d → ℤ =>
        ‖∫ y, UnitAddTorus.mFourier (-n) y * F y ∂cellMeasure d‖ ^ 2)
        (∫ y, ‖F y‖ ^ 2 ∂cellMeasure d) :=
      UnitAddTorus.hasSum_sq_mFourierCoeff F
    have hlim : (∫ y, ‖F y‖ ^ 2 ∂cellMeasure d) =
        ∫ y, (f y i) ^ 2 ∂cellMeasure d := by
      apply integral_congr_ae
      filter_upwards [L.coeFn_compLpL f] with y hy
      change ‖(L.compLpL 2 (cellMeasure d) f) y‖ ^ 2 = _
      rw [hy]
      change ‖(f y i : ℂ)‖ ^ 2 = _
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hlim] at hsum
    apply hsum.congr_fun
    intro n
    apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
    apply integral_congr_ae
    filter_upwards [L.coeFn_compLpL f] with y hy
    change UnitAddTorus.mFourier (-n) y * (f y i : ℂ) =
      UnitAddTorus.mFourier (-n) y * (L.compLpL 2 (cellMeasure d) f) y
    rw [hy]
    rfl
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hscalar i)
  have hnorm : (∑ i, ∫ y, (f y i) ^ 2 ∂cellMeasure d) = ‖f‖ ^ 2 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => ((Lp.memLp f).eval_piLp i).integrable_sq)]
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change (∑ i, (f y i) ^ 2) = ⟪f y, f y⟫_ℝ
      rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  rw [hnorm] at hsum
  simpa only [Finset.sum_apply] using hsum

end KVApproximation.Analysis
