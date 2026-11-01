import KVApproximation.KelvinVoigt.PronyProblem
import KVApproximation.KelvinVoigt.SpectralRepresentation
import KVApproximation.Spectral.RepresentationUniqueness
import KVApproximation.Approximation.UnweightedInterpolation
import KVApproximation.Approximation.UnweightedResponseIntegral
import KVApproximation.Approximation.ResponseMeasurability
import KVApproximation.Dynamics.PronyMeasurability

/-!
# Uniform error without spectral reweighting
-/

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Dynamics
open KVApproximation.Approximation

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hVorder hEorder

/-- Remark 4.6: the unweighted local construction has the stated elasticity-
contrast dependence. The bound retains the explicit constant from the proof. -/
theorem unweighted_prony_error_le (hδ : 0 < δ)
    (hspan : αE / βV < βE / αV) {m : ℕ} (hm : 0 < m) :
    uniformPronyError C
      (unweightedLocalModel S.measure (fun M => (C M).viscosity)
        (fun M => (C M).elasticity) (αE / βV) (βE / αV) m) δ ≤
      ENNReal.ofReal (unweightedErrorConstant (strainDimension d) δ (βE / αE) /
        (2 : ℝ) ^ (m - 1)) := by
  have hβV : 0 < βV := hαV.trans_le hVorder
  have hβE : 0 < βE := hαE.trans_le hEorder
  have hlower : 0 < αE / βV := div_pos hαE hβV
  let A := (4 * δ / (βV * Real.cos (3 / 4))) / (2 : ℝ) ^ (m - 1)
  let B := spectralVariationBound (strainDimension d) βV βE αE
  let P := unweightedLocalModel S.measure (fun M => (C M).viscosity)
    (fun M => (C M).elasticity) (αE / βV) (βE / αV) m
  have hcos : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B, spectralVariationBound]; positivity
  have hconstant : A * B = unweightedErrorConstant (strainDimension d) δ (βE / αE) /
      (2 : ℝ) ^ (m - 1) := by
    dsimp [A, B, spectralVariationBound, unweightedErrorConstant]
    field_simp
  rw [← hconstant]
  apply iSup_le
  intro M
  apply iSup_le
  intro e
  apply iSup_le
  intro he
  let ν := S.measure M
  have hrep := S.represents M
  have hmass : totalVariation ν Set.univ ≤ ENNReal.ofReal B := by
    obtain ⟨μ, hμpos, hμsupport, hμvar, hμkernel⟩ := spectral_representation
      (materialViscosity hαV M) (materialElasticity hαE M) (C M)
      hαV hβV hαE hβE (materialViscosity hαV M).bounds (materialElasticity hαE M).bounds
    have hμrep : IsSpectralRepresentation μ (C M).kernel (αE / βV) (βE / αV) :=
      ⟨hμpos, hμsupport, hμvar.trans_lt ENNReal.ofReal_lt_top, hμkernel⟩
    have heq := spectral_representation_unique hlower ν μ (C M).kernel hrep hμrep
    simpa only [heq] using hμvar
  have hmassreal : (totalVariation ν Set.univ).toReal ≤ B := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
    rwa [ENNReal.toReal_ofReal hB] at h
  have hmemory (t : ℝ) (ht : 0 ≤ t) :
      (∫ s in (0 : ℝ)..t, action ((C M).kernel (t - s)) (e.velocity s)) =
        tensorActionIntegral ν (realWeightedResponse 0 e t) :=
    memory_eq_unweightedResponseIntegral hlower ν (C M).kernel hrep e ht
  have hmeasMemory : AEStronglyMeasurable
      (fun t => ∫ s in (0 : ℝ)..t, action ((C M).kernel (t - s)) (e.velocity s))
      timeMeasure := by
    apply (aestronglyMeasurable_responseIntegral ν hrep.2.2.1 0 e).congr
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
      tensorActionIntegral ν (realWeightedResponse 0 e t) -
        tensorActionIntegral ν (partitionResponse 0 (αE / βV) (βE / αV) m e t) := by
    rw [show P.stress M e t = _ from unweighted_prony_stress_eq_partitionIntegral S.measure
      (fun M => (C M).viscosity) (fun M => (C M).elasticity) hlower m M
      hrep.2.1 hrep.2.2.1 e ht]
    unfold constitutiveStress
    rw [hmemory t ht]
    abel
  rw [heq]
  exact (norm_integrated_unweighted_partition_error_le ν hrep.2.2.1 hrep.2.1 e hβE hβV he
    hlower hspan ht hm).trans (mul_le_mul_of_nonneg_left hmassreal hA)

end KVApproximation.KelvinVoigt
