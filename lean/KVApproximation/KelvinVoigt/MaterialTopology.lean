module

public import KVApproximation.KelvinVoigt.MaterialFields
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Material topology and coefficient convergence
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

private theorem lp_one_tendsto {X F ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] [NormedAddCommGroup F]
    {l : Filter ι} {u : Lp F 2 μ} {us : ι → Lp F 2 μ}
    (hu : Tendsto us l (𝓝 u)) :
    Tendsto (fun n => eLpNorm (fun x => us n x - u x) 1 μ) l (𝓝 0) := by
  have htwo : Tendsto (fun n => eLpNorm (fun x => us n x - u x) 2 μ) l (𝓝 0) := by
    have hdist : Tendsto (fun n => edist (us n) u) l (𝓝 0) := by
      simpa only [edist_self] using hu.edist (tendsto_const_nhds (x := u))
    convert hdist using 1
    funext n
    exact (Lp.edist_def (us n) u).symm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htwo
    (fun _ => bot_le) (fun _ =>
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ENNReal) ≤ 2))

variable {d : ℕ} {αV βV γV αE βE γE : ℝ}
variable {ι : Type*} {l : Filter ι}
variable {M : admissibleMaterials d αV βV γV αE βE γE}
variable {Mseq : ι → admissibleMaterials d αV βV γV αE βE γE}

/-- Lemma B.2 and Proposition B.10: convergence in the common L² material
topology implies L¹ convergence of both coefficient fields. -/
theorem material_L1_tendsto (hM : Tendsto Mseq l (𝓝 M)) :
    Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y)
      1 (cellMeasure d)) l (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y)
      1 (cellMeasure d)) l (𝓝 0) := by
  have hraw := (continuous_subtype_val.tendsto M).comp hM
  exact ⟨lp_one_tendsto ((continuous_fst.tendsto _).comp hraw),
    lp_one_tendsto ((continuous_snd.tendsto _).comp hraw)⟩

/-- Corollary B.4 and Proposition B.10: the bounded representatives used
by the cell problems preserve this convergence. -/
theorem material_fields_L1_tendsto (hαV : 0 < αV) (hαE : 0 < αE)
    (hM : Tendsto Mseq l (𝓝 M)) :
    Tendsto (fun n => eLpNorm (fun y =>
      (materialViscosity hαV (Mseq n)).field y - (materialViscosity hαV M).field y)
        1 (cellMeasure d)) l (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun y =>
      (materialElasticity hαE (Mseq n)).field y - (materialElasticity hαE M).field y)
        1 (cellMeasure d)) l (𝓝 0) := by
  obtain ⟨hVconv, hEconv⟩ := material_L1_tendsto hM
  constructor
  · convert hVconv using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [(Mseq n).property.1.coeFn_toLp, M.property.1.coeFn_toLp] with y hy hz
    exact congrArg₂ (fun a b : Elasticity d => a - b) hy hz
  · convert hEconv using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [(Mseq n).property.2.1.coeFn_toLp, M.property.2.1.coeFn_toLp] with y hy hz
    exact congrArg₂ (fun a b : Elasticity d => a - b) hy hz

end KVApproximation.KelvinVoigt
