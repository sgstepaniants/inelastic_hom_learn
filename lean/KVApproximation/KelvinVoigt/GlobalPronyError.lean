import KVApproximation.KelvinVoigt.PronyProblem
import KVApproximation.Approximation.MemoryResponseIntegral
import KVApproximation.Approximation.GlobalInterpolation
import KVApproximation.Approximation.GlobalResponseIntegral
import KVApproximation.Approximation.ResponseMeasurability
import KVApproximation.Dynamics.PronyMeasurability
import KVApproximation.Homogenization.WeightedSpectralBound
import KVApproximation.Spectral.BoundEstimates

/-!
# Uniform error for one global logarithmic interpolant
-/

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Dynamics
open KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hVorder hEorder

/-- Remark 4.6: one weighted interpolant on the full logarithmic interval
has error of order `R * (1 + 1/R)^(-(n-1))` for every `R > 0`. -/
theorem global_prony_error_lt_of_span_pos (hd : 0 < d) (hδ : 0 < δ)
    (hspan : 0 < logarithmicSpan (αE / βV) (βE / αV)) {n : ℕ} (hn : 0 < n) :
    uniformPronyError C
      (globalPronyModel S.measure (fun M => (C M).viscosity)
        (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) n) δ <
      ENNReal.ofReal (globalPronyErrorBound (strainDimension d) δ
        (logarithmicSpan (αE / βV) (βE / αV)) n) := by
  have hβV : 0 < βV := hαV.trans_le hVorder
  have hβE : 0 < βE := hαE.trans_le hEorder
  have hlower : 0 < αE / βV := div_pos hαE hβV
  have hc : 0 < βE / βV := div_pos hβE hβV
  have hdim : 0 < strainDimension d := by
    unfold strainDimension
    exact Nat.div_pos (by nlinarith) (by decide)
  let R := logarithmicSpan (αE / βV) (βE / αV)
  have hRpos : 0 < R := hspan
  have horder : αE / βV < βE / αV := by
    apply (one_lt_div hlower).mp
    exact (Real.log_pos_iff (div_pos (div_pos hβE hαV) hlower).le).mp hRpos
  have hbase : 0 < 1 + 1 / R := by positivity
  let A := (4 * δ / βV * ellipseResponseFactor) * R / (1 + 1 / R) ^ (n - 1)
  let B := weightedVariationBound (strainDimension d) αV βV αE βE
  let P := globalPronyModel S.measure (fun M => (C M).viscosity) (fun M => (C M).elasticity)
    (βE / βV) (αE / βV) (βE / αV) n
  have hcos : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
  have hA : 0 < A := by
    dsimp [A, ellipseResponseFactor]
    positivity
  have hB : 0 ≤ B := by
    have hr : βV * αE / βE ≤ βV := (div_le_iff₀ hβE).mpr
      (mul_le_mul_of_nonneg_left hEorder hβV.le)
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have huniform : uniformPronyError C P δ ≤ ENNReal.ofReal (A * B) := by
    apply iSup_le
    intro M
    apply iSup_le
    intro e
    apply iSup_le
    intro he
    let μ := weightedMeasure (βE / βV) (S.measure M)
    have hrep := S.represents M
    obtain ⟨_, _, hsupport, hvar⟩ := weightedMeasure_properties hlower hc
      (S.measure M) hrep.1 hrep.2.1 hrep.2.2.1
    have hfinite : totalVariation μ Set.univ < ⊤ := hvar.trans_lt hrep.2.2.1
    have hmass := weightedMeasure_variation_le (materialViscosity hαV M)
      (materialElasticity hαE M) (C M) hαV hVorder hαE hEorder
      (materialViscosity hαV M).bounds (materialElasticity hαE M).bounds (S.measure M) hrep
    have hmassreal : (totalVariation μ Set.univ).toReal ≤ B := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
      rwa [ENNReal.toReal_ofReal hB] at h
    have hmemory (t : ℝ) (ht : 0 ≤ t) :
        (∫ s in (0 : ℝ)..t, action ((C M).kernel (t - s)) (e.velocity s)) =
          tensorActionIntegral μ (realWeightedResponse (βE / βV) e t) :=
      memory_eq_weightedResponseIntegral hlower hc (S.measure M) (C M).kernel hrep e ht
    have hmeasMemory : AEStronglyMeasurable
        (fun t => ∫ s in (0 : ℝ)..t, action ((C M).kernel (t - s)) (e.velocity s))
        timeMeasure := by
      apply (aestronglyMeasurable_responseIntegral μ hfinite (βE / βV) e).congr
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact (hmemory t ht).symm
    have hmeasC : AEStronglyMeasurable (constitutiveStress (C M) e) timeMeasure :=
      ((actionL d (C M).viscosity).continuous.comp_aestronglyMeasurable
        e.velocity_memLp.aestronglyMeasurable).add
        ((actionL d (C M).elasticity).continuous.comp_aestronglyMeasurable
          e.value_memLp.aestronglyMeasurable) |>.add hmeasMemory
    have hdiff : AEStronglyMeasurable
        (fun t => constitutiveStress (C M) e t - P.stress M e t) timeMeasure :=
      hmeasC.sub (aestronglyMeasurable_pronyStress P M e)
    rw [eLpNorm_exponent_top hdiff]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have heq : constitutiveStress (C M) e t - P.stress M e t =
        tensorActionIntegral μ (realWeightedResponse (βE / βV) e t) -
          tensorActionIntegral μ (globalResponseInterpolant (βE / βV) (αE / βV) (βE / αV) n e t) := by
      rw [show P.stress M e t = _ from global_prony_stress_eq_responseIntegral S.measure
        (fun M => (C M).viscosity) (fun M => (C M).elasticity) hlower hc n M
        hrep.1 hrep.2.1 hrep.2.2.1 e ht]
      unfold constitutiveStress
      rw [hmemory t ht]
      abel
    rw [heq]
    exact (norm_integrated_global_response_error_le_of_span_pos μ hfinite hsupport e hβE hβV he
      hlower horder hspan ht hn).trans (mul_le_mul_of_nonneg_left hmassreal hA.le)
  have hconstant : A * (2 * (strainDimension d : ℝ) * βV) =
      globalPronyErrorBound (strainDimension d) δ R n := by
    dsimp [A, globalPronyErrorBound, pronyConstant]
    field_simp; ring
  have hpositive : 0 < globalPronyErrorBound (strainDimension d) δ R n := by
    rw [← hconstant]
    exact mul_pos hA (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hdim)) hβV)
  apply huniform.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hpositive).mpr
  exact (mul_lt_mul_of_pos_left (weightedVariationBound_lt hdim hαV hβV hαE hβE) hA)
    |>.trans_eq hconstant
/-- Remark 4.6: one weighted interpolant on the full logarithmic interval
has error of order `R * (1 + 1/R)^(-(n-1))` for `R ≥ 1`. -/
theorem global_prony_error_lt (hd : 0 < d) (hδ : 0 < δ)
    (hspan : 1 ≤ logarithmicSpan (αE / βV) (βE / αV)) {n : ℕ} (hn : 0 < n) :
    uniformPronyError C
      (globalPronyModel S.measure (fun M => (C M).viscosity)
        (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) n) δ <
      ENNReal.ofReal (globalPronyErrorBound (strainDimension d) δ
        (logarithmicSpan (αE / βV) (βE / αV)) n) := by
  exact global_prony_error_lt_of_span_pos hαV hVorder hαE hEorder C S hd hδ
    (lt_of_lt_of_le zero_lt_one hspan) hn

end KVApproximation.KelvinVoigt
