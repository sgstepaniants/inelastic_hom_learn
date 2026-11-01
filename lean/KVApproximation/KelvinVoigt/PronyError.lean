import KVApproximation.KelvinVoigt.PronyProblem
import KVApproximation.Approximation.MemoryResponseIntegral
import KVApproximation.Approximation.PronyResponseIntegral
import KVApproximation.Approximation.PartitionResponseIntegration
import KVApproximation.Approximation.ResponseMeasurability
import KVApproximation.Dynamics.PronyMeasurability
import KVApproximation.Homogenization.WeightedSpectralBound
import KVApproximation.Spectral.BoundEstimates

/-!
# Uniform Prony approximation of the constitutive stress
-/

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Dynamics
open KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hVorder hEorder

/-- Proposition B.10 (`eq:prony_homogenized_error_uniform`): the strict
uniform error bound is taken after both material and strain supremums. -/
theorem local_prony_error_lt (hd : 0 < d) (hδ : 0 < δ)
    (hspan : αE / βV < βE / αV) {m : ℕ} (hm : 0 < m) :
    uniformPronyError C
      (localPronyModel S.measure (fun M => (C M).viscosity) (fun M => (C M).elasticity)
        (βE / βV) (αE / βV) (βE / αV) m) δ <
      ENNReal.ofReal (pronyErrorBound (strainDimension d) δ m) := by
  have hβV : 0 < βV := hαV.trans_le hVorder
  have hβE : 0 < βE := hαE.trans_le hEorder
  have hlower : 0 < αE / βV := div_pos hαE hβV
  have hc : 0 < βE / βV := div_pos hβE hβV
  have hn : 0 < strainDimension d := by
    unfold strainDimension
    exact Nat.div_pos (by nlinarith) (by decide)
  let A := localResponseErrorBound δ βV m
  let B := weightedVariationBound (strainDimension d) αV βV αE βE
  let P := localPronyModel S.measure (fun M => (C M).viscosity) (fun M => (C M).elasticity)
    (βE / βV) (αE / βV) (βE / αV) m
  have hcos : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
  have hA : 0 < A := by
    dsimp [A, localResponseErrorBound, ellipseResponseFactor]
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
          tensorActionIntegral μ (partitionResponse (βE / βV) (αE / βV) (βE / αV) m e t) := by
      rw [show P.stress M e t = _ from local_prony_stress_eq_partitionIntegral S.measure
        (fun M => (C M).viscosity) (fun M => (C M).elasticity) hlower hc m M
        hrep.1 hrep.2.1 hrep.2.2.1 e ht]
      unfold constitutiveStress
      rw [hmemory t ht]
      abel
    rw [heq]
    exact (norm_integrated_partition_error_le μ hfinite hsupport e hβE hβV he
      hlower hspan ht hm).trans (mul_le_mul_of_nonneg_left hmassreal hA.le)
  have hconstant : A * (2 * (strainDimension d : ℝ) * βV) =
      pronyErrorBound (strainDimension d) δ m := by
    dsimp [A, localResponseErrorBound, pronyErrorBound, pronyConstant]
    field_simp
    ring
  have hpositive : 0 < pronyErrorBound (strainDimension d) δ m := by
    rw [← hconstant]
    exact mul_pos hA (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hn)) hβV)
  apply huniform.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hpositive).mpr
  exact (mul_lt_mul_of_pos_left (weightedVariationBound_lt hn hαV hβV hαE hβE) hA)
    |>.trans_eq hconstant

end KVApproximation.KelvinVoigt
