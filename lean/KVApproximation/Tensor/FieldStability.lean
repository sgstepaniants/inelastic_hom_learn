module

public import KVApproximation.Tensor.FieldNormBounds
public import KVApproximation.Analysis.MultiplicationConvergence
public import KVApproximation.Analysis.PeriodicVariationStability

/-!
# Closed coefficient constraints

The common Frobenius bound first supplies an essentially bounded limit.
Strong convergence of multiplication then preserves the quadratic-form bounds,
while distributional testing preserves the full periodic BV norm.
-/

public section

open MeasureTheory Filter
open scoped Topology InnerProductSpace
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Lemma B.2 (`lem:bv_compact`), closedness step: an L¹ limit preserves
the essential boundedness, quadratic-form bounds and full periodic BV bound. -/
theorem coefficient_constraints_of_tendsto_L1 {d : ℕ}
    {A : CoefficientField d 1} {Aseq : ℕ → CoefficientField d 1}
    {α β : ℝ} {C : ENNReal} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hseq : ∀ n, MemLp (Aseq n) ⊤ (cellMeasure d) ∧
      HasFieldBounds α β (Aseq n) ∧ periodicBVNorm (Aseq n) ≤ C)
    (hconv : Tendsto Aseq atTop (𝓝 A)) :
    MemLp A ⊤ (cellMeasure d) ∧ HasFieldBounds α β A ∧ periodicBVNorm A ≤ C := by
  let Bseq (n : ℕ) : CoefficientField d ⊤ := (hseq n).1.toLp (Aseq n)
  have hBseq (n : ℕ) : HasFieldBounds α β (Bseq n) :=
    (hseq n).2.1.congr (hseq n).1.coeFn_toLp.symm
  let κ := Real.sqrt (strainDimension d) * β
  have hκ : 0 ≤ κ := mul_nonneg (Real.sqrt_nonneg _) hβ
  have hbounded (n : ℕ) : eLpNorm (Bseq n) ⊤ (cellMeasure d) ≤
      ENNReal.ofReal κ := (hBseq n).eLpNorm_top_le (Bseq n) hα hβ
  have hboundedA (n : ℕ) : eLpNorm (Aseq n) ⊤ (cellMeasure d) ≤
      ENNReal.ofReal κ := by
    rw [← eLpNorm_congr_ae (hseq n).1.coeFn_toLp]
    exact hbounded n
  have hA := (multiplication_converges hκ hboundedA hconv).1
  let B : CoefficientField d ⊤ := hA.toLp A
  have hnorm : Tendsto
      (fun n => eLpNorm (fun y => Bseq n y - B y) 1 (cellMeasure d)) atTop (𝓝 0) := by
    have heq (n : ℕ) : eLpNorm (fun y => Bseq n y - B y) 1 (cellMeasure d) =
        edist (Aseq n) A := by
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae ((hseq n).1.coeFn_toLp.sub hA.coeFn_toLp)
    simp only [heq]
    simpa only [edist_self] using
      Filter.Tendsto.edist (α := CoefficientField d 1) hconv
        (tendsto_const_nhds (x := A))
  have hB : HasFieldBounds α β B := by
    intro e
    have hmul := multiplication_strong_tendsto B Bseq hκ hbounded hnorm e
    have he : Tendsto (fun n => fieldPairing (Bseq n) e e) atTop
        (𝓝 (fieldPairing B e e)) := by
      have hi := hmul.inner (𝕜 := ℝ) (tendsto_const_nhds (x := e))
      simpa only [← boundedFieldForm_apply, boundedFieldForm,
        ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hi
    exact ⟨ge_of_tendsto he (Eventually.of_forall fun n => (hBseq n e).1),
      le_of_tendsto he (Eventually.of_forall fun n => (hBseq n e).2)⟩
  exact ⟨hA, hB.congr hA.coeFn_toLp,
    periodicBVNorm_le_of_tendsto_L1 hconv (fun n => (hseq n).2.2)⟩

end KVApproximation.Tensor
