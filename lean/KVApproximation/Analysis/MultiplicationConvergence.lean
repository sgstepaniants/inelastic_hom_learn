module

public import KVApproximation.Analysis.LpConvergence
public import KVApproximation.Tensor.MultiplicationIdentities
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Strong convergence of tensor multiplication

Lemma B.1 first passes the common essential bound to the L¹ limit. For every
subsequence, convergence in measure supplies a further almost-everywhere
convergent subsequence. Frobenius contraction and dominated convergence then
give the L² conclusion.
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis

namespace KVApproximation.Tensor

/-- Lemma B.1: the essential-supremum bound holds pointwise almost everywhere. -/
private theorem ae_norm_le_of_eLpNorm_top_le {d : ℕ}
    (A : CoefficientField d 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hA : eLpNorm A ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ) :
    ∀ᵐ y ∂cellMeasure d, ‖A y‖ ≤ κ := by
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable A)] at hA
  filter_upwards [ae_le_eLpNormEssSup (f := A) (μ := cellMeasure d)] with y hy
  apply (ENNReal.ofReal_le_ofReal_iff hκ).mp
  simpa only [ofReal_norm] using hy.trans hA

/-- Lemma B.1 (`lem:strong_conv_tensor`): uniform essential boundedness
and L¹ convergence imply strong convergence of tensor multiplication on L². -/
theorem multiplication_converges {d : ℕ}
    {A : CoefficientField d 1} {Aseq : ℕ → CoefficientField d 1}
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hbounded : ∀ n, eLpNorm (Aseq n) ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ)
    (hconv : Tendsto Aseq atTop (𝓝 A)) :
    MemLp A ⊤ (cellMeasure d) ∧
      eLpNorm A ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ ∧
      ∀ e : StrainField d,
        Tendsto (fun n => eLpNorm
          (fun y => action (Aseq n y - A y) (e y)) 2 (cellMeasure d))
          atTop (𝓝 0) := by
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hconv
  have hA : eLpNorm A ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ :=
    eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hbounded) hmeasure
      (fun n => Lp.aestronglyMeasurable (Aseq n))
  refine ⟨hA.trans_lt ENNReal.ofReal_lt_top, hA, fun e => ?_⟩
  have hbA := ae_norm_le_of_eLpNorm_top_le A hκ hA
  have hbseq (n : ℕ) := ae_norm_le_of_eLpNorm_top_le (Aseq n) hκ (hbounded n)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hms⟩ := (hmeasure.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply tendsto_eLpNorm_of_dominated_zero (by norm_num) (by norm_num)
    (bound := fun y => (2 * κ) * ‖e y‖)
  · intro n
    exact (actionL d).aestronglyMeasurable_comp₂
      ((Lp.aestronglyMeasurable (Aseq (ns (ms n)))).sub (Lp.aestronglyMeasurable A))
      (Lp.aestronglyMeasurable e)
  · exact (Lp.memLp e).norm.const_mul (2 * κ)
  · intro n
    filter_upwards [hbseq (ns (ms n)), hbA] with y hn hy
    calc
      ‖action (Aseq (ns (ms n)) y - A y) (e y)‖ ≤
          ‖Aseq (ns (ms n)) y - A y‖ * ‖e y‖ := norm_action_le _ _
      _ ≤ (2 * κ) * ‖e y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          _ ≤ ‖Aseq (ns (ms n)) y‖ + ‖A y‖ := norm_sub_le _ _
          _ ≤ 2 * κ := by linarith
      _ ≤ ‖(2 * κ) * ‖e y‖‖ := Real.le_norm_self _
  · filter_upwards [hms] with y hy
    have h := ((actionL d).flip (e y)).continuous.tendsto 0
    have hsub : Tendsto (fun n => Aseq (ns (ms n)) y - A y) atTop (𝓝 0) := by
      simpa only [Function.comp_def, sub_self] using hy.sub (tendsto_const_nhds (x := A y))
    have hz := h.comp hsub
    simpa only [Function.comp_def, ContinuousLinearMap.map_zero,
      ContinuousLinearMap.flip_apply, actionL_apply]
      using hz

/-- Lemma B.1, as used in Proposition B.3: the actual L² multiplication
operators converge strongly under a common essential bound and L¹ convergence. -/
theorem multiplication_strong_tendsto {d : ℕ}
    (A : CoefficientField d ⊤) (Aseq : ℕ → CoefficientField d ⊤)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hbounded : ∀ n, eLpNorm (Aseq n) ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ)
    (hconv : Tendsto
      (fun n => eLpNorm (fun y => Aseq n y - A y) 1 (cellMeasure d)) atTop (𝓝 0))
    (e : StrainField d) :
    Tendsto (fun n => multiplication (Aseq n) e) atTop (𝓝 (multiplication A e)) := by
  let hA : MemLp A 1 (cellMeasure d) := (Lp.memLp A).mono_exponent (by simp)
  let hseq (n : ℕ) : MemLp (Aseq n) 1 (cellMeasure d) :=
    (Lp.memLp (Aseq n)).mono_exponent (by simp)
  let B : CoefficientField d 1 := hA.toLp A
  let Bseq (n : ℕ) : CoefficientField d 1 := (hseq n).toLp (Aseq n)
  have hB : Tendsto Bseq atTop (𝓝 B) := by
    apply tendsto_iff_dist_tendsto_zero.2
    have heq (n : ℕ) : dist (Bseq n) B =
        (eLpNorm (fun y => Aseq n y - A y) 1 (cellMeasure d)).toReal := by
      rw [Lp.dist_def]
      congr 1
      exact eLpNorm_congr_ae ((hseq n).coeFn_toLp.sub hA.coeFn_toLp)
    simp only [heq]
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hconv
  have hb (n : ℕ) : eLpNorm (Bseq n) ⊤ (cellMeasure d) ≤ ENNReal.ofReal κ := by
    rw [eLpNorm_congr_ae (hseq n).coeFn_toLp]
    exact hbounded n
  have hmul := (multiplication_converges hκ hb hB).2.2 e
  apply tendsto_iff_dist_tendsto_zero.2
  have heq (n : ℕ) : dist (multiplication (Aseq n) e) (multiplication A e) =
      (eLpNorm (fun y => action (Bseq n y - B y) (e y)) 2 (cellMeasure d)).toReal := by
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [multiplication_apply_ae (Aseq n) e, multiplication_apply_ae A e,
      (hseq n).coeFn_toLp, hA.coeFn_toLp] with y hn hy hbn hby
    change Bseq n y = Aseq n y at hbn
    change B y = A y at hby
    simp only [Pi.sub_apply, hn, hy, hbn, hby, ← actionL_apply, map_sub, sub_apply]
  simp only [heq]
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hmul

end KVApproximation.Tensor
