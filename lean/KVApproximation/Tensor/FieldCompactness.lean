module

public import KVApproximation.Tensor.FieldStability
public import KVApproximation.Analysis.PeriodicBVCompactness
public import KVApproximation.Analysis.LpInterpolation

/-!
# Compact coefficient classes

A bounded BV sequence has an L¹-convergent subsequence. Its common Frobenius
bound passes to the limit and upgrades convergence to L² by interpolation.
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Lemma B.2 (`lem:bv_compact`): the compact L² coefficient class before
taking the product of viscosity and elasticity fields. -/
theorem isCompact_coefficient_constraints {d : ℕ} {α β : ℝ} {C : ENNReal}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hC : C ≠ ⊤) :
    IsCompact {A : CoefficientField d 2 | MemLp A ⊤ (cellMeasure d) ∧
      HasFieldBounds α β A ∧ periodicBVNorm A ≤ C} := by
  apply IsSeqCompact.isCompact
  intro Aseq hseq
  let hL1 (n : ℕ) : MemLp (Aseq n) 1 (cellMeasure d) :=
    (Lp.memLp (Aseq n)).mono_exponent (by norm_num)
  let Bseq (n : ℕ) : CoefficientField d 1 := (hL1 n).toLp (Aseq n)
  have hBseq (n : ℕ) : MemLp (Bseq n) ⊤ (cellMeasure d) ∧
      HasFieldBounds α β (Bseq n) ∧ periodicBVNorm (Bseq n) ≤ C := by
    refine ⟨(hseq n).1.ae_eq (hL1 n).coeFn_toLp.symm,
      (hseq n).2.1.congr (hL1 n).coeFn_toLp.symm, ?_⟩
    rw [periodicBVNorm_congr (hL1 n).coeFn_toLp]
    exact (hseq n).2.2
  obtain ⟨B, hB, ns, hns, hconv⟩ :=
    (isCompact_periodicBV_sublevel (d := d) (F := Elasticity d) hC).isSeqCompact
      (fun n => (hBseq n).2.2)
  obtain ⟨hBtop, hBbounds, hBBV⟩ := coefficient_constraints_of_tendsto_L1 hα hβ
    (fun n => hBseq (ns n)) hconv
  let hB2 : MemLp B 2 (cellMeasure d) := hBtop.mono_exponent (by simp)
  let A : CoefficientField d 2 := hB2.toLp B
  have hA : MemLp A ⊤ (cellMeasure d) ∧
      HasFieldBounds α β A ∧ periodicBVNorm A ≤ C := by
    refine ⟨hBtop.ae_eq hB2.coeFn_toLp.symm,
      hBbounds.congr hB2.coeFn_toLp.symm, ?_⟩
    rw [periodicBVNorm_congr hB2.coeFn_toLp]
    exact hBBV
  refine ⟨A, hA, ns, hns, ?_⟩
  let κ := Real.sqrt (strainDimension d) * β
  have hκ : 0 ≤ κ := mul_nonneg (Real.sqrt_nonneg _) hβ
  have hpoint (U : PeriodicCell d → Elasticity d)
      (hU : MemLp U ⊤ (cellMeasure d)) (hUb : HasFieldBounds α β U) :
      ∀ᵐ y ∂cellMeasure d, ‖U y‖ ≤ κ := by
    let Utop : CoefficientField d ⊤ := hU.toLp U
    have hb : HasFieldBounds α β Utop := hUb.congr hU.coeFn_toLp.symm
    have hp := (hasFieldBounds_iff_ae Utop).1 hb
    filter_upwards [hp, hU.coeFn_toLp] with y hy heq
    rw [← heq]
    exact hy.norm_le_sqrt_dimension hα hβ
  have hdiffBound (n : ℕ) : ∀ᵐ y ∂cellMeasure d,
      ‖Aseq (ns n) y - A y‖ ≤ 2 * κ := by
    filter_upwards [hpoint (Aseq (ns n)) (hseq (ns n)).1 (hseq (ns n)).2.1,
      hpoint A hA.1 hA.2.1] with y hn hy
    have ht := norm_sub_le (Aseq (ns n) y) (A y)
    linarith
  have hL1conv : Tendsto
      (fun n => eLpNorm (fun y => Aseq (ns n) y - A y) 1 (cellMeasure d))
      atTop (𝓝 0) := by
    have heq (n : ℕ) : eLpNorm (fun y => Aseq (ns n) y - A y) 1 (cellMeasure d) =
        edist (Bseq (ns n)) B := by
      rw [Lp.edist_def]
      exact (eLpNorm_congr_ae ((hL1 (ns n)).coeFn_toLp.sub hB2.coeFn_toLp.symm)).symm
    simp only [heq]
    simpa only [Function.comp_def, edist_self] using
      Filter.Tendsto.edist (α := CoefficientField d 1) hconv
        (tendsto_const_nhds (x := B))
  have hL2conv := tendsto_eLpNorm_two_of_one_of_ae_bound
    (fun n => (Lp.aestronglyMeasurable (Aseq (ns n))).sub (Lp.aestronglyMeasurable A))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ) hdiffBound hL1conv
  apply tendsto_iff_dist_tendsto_zero.2
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hL2conv
  simpa only [Function.comp_def, Lp.dist_def, ENNReal.toReal_zero] using ht

end KVApproximation.Tensor
