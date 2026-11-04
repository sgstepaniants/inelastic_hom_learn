module

public import KVApproximation.KelvinVoigt.StripMaterials
public import KVApproximation.KelvinVoigt.StripSpectralEdges

/-!
# Discontinuity of the relaxation operator's upper spectral edge
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`): the thin-strip construction
belongs to one BV-bounded material class, converges in both L¹ and L², and has
spectral edge two while the limit has edge one. The final conclusion is failure
of continuity on that actual material class. -/
theorem spectral_edge_discontinuous {d : ℕ}
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (i : Fin d) :
    ∃ γV γE : ℝ, 0 < γV ∧ 0 < γE ∧
      ∃ M : admissibleMaterials d 1 1 γV 1 2 γE,
      ∃ Mseq : ℕ → admissibleMaterials d 1 1 γV 1 2 γE,
        (∀ᵐ y ∂cellMeasure d, M.val.1 y = identityElasticity d ∧
          M.val.2 y = identityElasticity d) ∧
        (∀ n, ∀ᵐ y ∂cellMeasure d,
          (Mseq n).val.1 y = identityElasticity d ∧
            (Mseq n).val.2 y = stripElasticity i n y) ∧
        Tendsto (fun n => (Mseq n).val) atTop (𝓝 M.val) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y)
          1 (cellMeasure d)) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y)
          1 (cellMeasure d)) atTop (𝓝 0) ∧
        materialSpectralEdge (by norm_num) (by norm_num) M = 1 ∧
        (∀ n, materialSpectralEdge (by norm_num) (by norm_num) (Mseq n) = 2) ∧
        ¬ Continuous (materialSpectralEdge (d := d) (γV := γV) (γE := γE)
          (βV := 1) (βE := 2) (show (0 : ℝ) < 1 by norm_num)
          (show (0 : ℝ) < 1 by norm_num)) := by
  obtain ⟨M, Mseq, hM, hMs, hconv, hL1V, hL1E⟩ := exists_strip_material_family i
  have hγV : 0 < ‖identityElasticity d‖ + 1 :=
    add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  have hγE : 0 < 4 * ‖identityElasticity d‖ + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) (norm_nonneg _)) zero_lt_one
  have hedge : materialSpectralEdge (by norm_num) (by norm_num) M = 1 :=
    materialSpectralEdge_identity i M
      (hM.mono fun _ h => h.1) (hM.mono fun _ h => h.2)
  have hedges (n : ℕ) : materialSpectralEdge (by norm_num) (by norm_num) (Mseq n) = 2 :=
    materialSpectralEdge_strip i n (Mseq n)
      ((hMs n).mono fun _ h => h.1) ((hMs n).mono fun _ h => h.2)
  refine ⟨_, _, hγV, hγE, M, Mseq, hM, hMs,
    tendsto_subtype_rng.1 hconv, hL1V, hL1E, hedge, hedges, ?_⟩
  intro hcontinuous
  have hlim := (hcontinuous.tendsto M).comp hconv
  have htwo : Tendsto
      (fun n => materialSpectralEdge (by norm_num) (by norm_num) (Mseq n))
      atTop (𝓝 (2 : ℝ)) := by
    simpa only [hedges] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2))
  have hcontradiction := tendsto_nhds_unique hlim htwo
  rw [hedge] at hcontradiction
  norm_num at hcontradiction

end KVApproximation.KelvinVoigt
