module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import KVApproximation.KelvinVoigt.PronyProblem
public import KVApproximation.Tensor.MandelFiniteIsometry
public import KVApproximation.KelvinVoigt.MaterialResponseApproximation
public import KVApproximation.NeuralOperators.UniformPronyStability
public import KVApproximation.Dynamics.PronyStateBounds
public import KVApproximation.Approximation.PronyIdentities

/-!
# Stability of material-dependent neural responses
-/

public section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Approximation
open KVApproximation.Dynamics KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
variable {αV βV γV αE βE γE δ η εF εG : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
variable (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE)
variable (hδ : 0 < δ) (hη : 0 < η) (hεF : 0 < εF) (hεG : 0 < εG)
variable (hmargin : εG ≤ (αE / βV) * η)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hd hVorder hγV hEorder hγE hδ hη hεF hεG hmargin

/-- Proposition B.13 (`prop:ua_step3_stability`, `eq:ua_err`), with the
local Prony model and the response mappings supplied by Lemma B.12.
The scalar state uses the prescribed block Mandel isometry. -/
theorem local_prony_responses_stable (hspan : αE / βV < βE / αV)
    {m : ℕ} (hm : 0 < m) :
    let n := logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)) * m
    let P := localPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) m
    ∀ (Fclass : StressResponseClass d (n * strainDimension d))
      (Gclass : KineticResponseClass d (n * strainDimension d)),
      HasUniversalApproximation Fclass → HasLocallyLipschitzApproximation Gclass →
      ∃ T : BlockState n (Symmetric d) ≃ₗᵢ[ℝ] InternalState (n * strainDimension d),
        (∀ q, T q = scalarBlockStrainMandel q) ∧
        ∃ F ∈ Fclass, ∃ G ∈ Gclass,
          ∃ q : admissibleMaterials d αV βV γV αE βE γE →
            {e : BoundedTrajectory (Symmetric d) // e.Admissible βE βV δ} →
              BoundedTrajectory (InternalState (n * strainDimension d)),
            (∀ M e, IsResponseSolution G M.val e.val (q M e) ∧
              ∀ q', IsResponseSolution G M.val e.val q' → (q M e).Agree q') ∧
            (⨆ M, ⨆ e, eLpNorm (fun t => (q M e).value t - T (P.state M e.val t))
              ⊤ timeMeasure) ≤ ENNReal.ofReal (εG / (αE / βV)) ∧
            (⨆ M, ⨆ e, eLpNorm
              (fun t => stressAlong F M.val e.val (q M e) t - P.stress M e.val t)
              ⊤ timeMeasure) ≤ ENNReal.ofReal (εF + Real.sqrt n * εG / (αE / βV)) := by
  dsimp only
  intro Fclass Gclass hF hG
  let P := localPronyModel S.measure (fun M => (C M).viscosity)
    (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) m
  let : CompactSpace (admissibleMaterials d αV βV γV αE βE γE) :=
    isCompact_iff_compactSpace.mp
      (isCompact_admissibleMaterials hd hαV hVorder hγV hαE hEorder hγE)
  have hlower : 0 < αE / βV := div_pos hαE (hαV.trans_le hVorder)
  have hrate (k) : αE / βV ≤ P.rate k :=
    (localPronyRate_mem hlower hspan hm
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).1
  obtain ⟨δIV, hδIV, hIV⟩ := prony_state_uniform_bound P Set.univ isCompact_univ
    (fun k => ((actionL d).continuous.comp
      (continuous_local_prony_coefficient hαV hVorder hαE hEorder C S hspan hm
        (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)).continuousOn)
    (hαE.trans_le hEorder) (hαV.trans_le hVorder) hδ
    (fun k => hlower.trans_le (hrate k))
  obtain ⟨T, hT, F, hFmem, G, hGmem, hFapprox, hGapprox, hGlip⟩ :=
    local_prony_responses_approximate hd hαV hVorder hγV hαE hEorder hγE
      hδ hδIV hη hεF hεG C S hspan hm Fclass Gclass hF hG
  refine ⟨T, hT, F, hFmem, G, hGmem, ?_⟩
  exact uniform_prony_response_stability P Subtype.val T
    (hαE.trans_le hEorder) (hαV.trans_le hVorder) hlower hrate hδIV
    (fun a => hIV a (Set.mem_univ a)) hη hεF hεG hmargin
    F G hGlip hFapprox hGapprox

/-- Proposition B.13, singleton spectral interval: the exact one-term
Prony model has the same global existence, uniqueness and uniform error
bounds, with `strainDimension d` scalar states. -/
theorem singleton_prony_responses_stable (hspan : αE / βV = βE / αV) :
    let P := singletonPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (αE / βV)
    ∀ (Fclass : StressResponseClass d (1 * strainDimension d))
      (Gclass : KineticResponseClass d (1 * strainDimension d)),
      HasUniversalApproximation Fclass → HasLocallyLipschitzApproximation Gclass →
      ∃ T : BlockState 1 (Symmetric d) ≃ₗᵢ[ℝ] InternalState (1 * strainDimension d),
        (∀ q, T q = scalarBlockStrainMandel q) ∧
        ∃ F ∈ Fclass, ∃ G ∈ Gclass,
          ∃ q : admissibleMaterials d αV βV γV αE βE γE →
            {e : BoundedTrajectory (Symmetric d) // e.Admissible βE βV δ} →
              BoundedTrajectory (InternalState (1 * strainDimension d)),
            (∀ M e, IsResponseSolution G M.val e.val (q M e) ∧
              ∀ q', IsResponseSolution G M.val e.val q' → (q M e).Agree q') ∧
            (⨆ M, ⨆ e, eLpNorm (fun t => (q M e).value t - T (P.state M e.val t))
              ⊤ timeMeasure) ≤ ENNReal.ofReal (εG / (αE / βV)) ∧
            (⨆ M, ⨆ e, eLpNorm
              (fun t => stressAlong F M.val e.val (q M e) t - P.stress M e.val t)
              ⊤ timeMeasure) ≤ ENNReal.ofReal (εF + εG / (αE / βV)) := by
  dsimp only
  intro Fclass Gclass hF hG
  let P := singletonPronyModel S.measure (fun M => (C M).viscosity)
    (fun M => (C M).elasticity) (αE / βV)
  let : CompactSpace (admissibleMaterials d αV βV γV αE βE γE) :=
    isCompact_iff_compactSpace.mp
      (isCompact_admissibleMaterials hd hαV hVorder hγV hαE hEorder hγE)
  have hlower : 0 < αE / βV := div_pos hαE (hαV.trans_le hVorder)
  obtain ⟨δIV, hδIV, hIV⟩ := prony_state_uniform_bound P Set.univ isCompact_univ
    (fun _ => ((actionL d).continuous.comp
      (continuous_singleton_prony_coefficient hαV hVorder hαE hEorder C S hspan)).continuousOn)
    (hαE.trans_le hEorder) (hαV.trans_le hVorder) hδ (fun _ => hlower)
  obtain ⟨T, hT, F, hFmem, G, hGmem, hFapprox, hGapprox, hGlip⟩ :=
    singleton_prony_responses_approximate hd hαV hVorder hγV hαE hEorder hγE
      hδ hδIV hη hεF hεG C S hspan Fclass Gclass hF hG
  refine ⟨T, hT, F, hFmem, G, hGmem, ?_⟩
  simpa only [Nat.cast_one, Real.sqrt_one, one_mul] using
    uniform_prony_response_stability P Subtype.val T
      (hαE.trans_le hEorder) (hαV.trans_le hVorder) hlower (fun _ => le_rfl) hδIV
      (fun a => hIV a (Set.mem_univ a)) hη hεF hεG hmargin
      F G hGlip hFapprox hGapprox

end KVApproximation.KelvinVoigt
