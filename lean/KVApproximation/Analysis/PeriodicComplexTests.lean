module

public import KVApproximation.Analysis.PeriodicSmoothIdentities
public import KVApproximation.Analysis.PeriodicSobolev
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Complex tests for real periodic weak derivatives
-/

public section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Section 3.1, periodic Sobolev foundations: real weak derivatives may be
tested against a complex periodic field by its real and imaginary parts. -/
theorem HasPeriodicWeakGradient.integral_complex_test {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g : Lp (SecondOrder d) 2 (cellMeasure d)}
    (h : HasPeriodicWeakGradient u g) (φ : PeriodicC1 d ℂ) (i j : Fin d) :
    (∫ y, u y i • φ.partial j y ∂cellMeasure d) =
      -(∫ y, g y (i, j) • φ.value y ∂cellMeasure d) := by
  have hp : MemLp (φ.partial j) 2 (cellMeasure d) :=
    (φ.continuous_partial j).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hv : MemLp φ.value 2 (cellMeasure d) :=
    φ.continuous_value.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h₁ : Integrable (fun y => u y i • φ.partial j y) (cellMeasure d) :=
    memLp_one_iff_integrable.mp (((Lp.memLp u).eval_piLp i).smul hp)
  have h₂ : Integrable (fun y => g y (i, j) • φ.value y) (cellMeasure d) :=
    memLp_one_iff_integrable.mp (((Lp.memLp g).eval_piLp (i, j)).smul hv)
  have htest (L : ℂ →L[ℝ] ℝ) :
      L (∫ y, u y i • φ.partial j y ∂cellMeasure d) =
        -L (∫ y, g y (i, j) • φ.value y ∂cellMeasure d) := by
    let ψ : PeriodicC1 d ℝ :=
      ⟨fun y => L (φ.value y), L.contDiff.comp φ.contDiff_lift⟩
    have hpartial (y : PeriodicCell d) : ψ.partial j y = L (φ.partial j y) := by
      have hd := L.hasFDerivAt.comp (cellRepresentative y)
        (φ.contDiff_lift.differentiable one_ne_zero (cellRepresentative y)).hasFDerivAt
      simp only [Function.comp_def] at hd
      change fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => L (φ.value (toCell x)))
        (cellRepresentative y) (WithLp.toLp 2 (Pi.single j (1 : ℝ))) = _
      rw [hd.fderiv]
      rfl
    have hψ := h ψ i j
    simp_rw [hpartial] at hψ
    rw [← L.integral_comp_comm h₁, ← L.integral_comp_comm h₂]
    simp_rw [map_smul, smul_eq_mul]
    exact hψ
  apply Complex.ext
  · change Complex.reCLM (∫ y, u y i • φ.partial j y ∂cellMeasure d) =
      Complex.reCLM (-(∫ y, g y (i, j) • φ.value y ∂cellMeasure d))
    rw [map_neg]
    exact htest Complex.reCLM
  · change Complex.imCLM (∫ y, u y i • φ.partial j y ∂cellMeasure d) =
      Complex.imCLM (-(∫ y, g y (i, j) • φ.value y ∂cellMeasure d))
    rw [map_neg]
    exact htest Complex.imCLM

end KVApproximation.Analysis
