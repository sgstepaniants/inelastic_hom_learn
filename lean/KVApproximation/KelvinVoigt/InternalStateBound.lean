module

public import KVApproximation.KelvinVoigt.MaterialCompactness
public import KVApproximation.KelvinVoigt.MaterialResponseContinuity
public import KVApproximation.Approximation.PronyIdentities
public import KVApproximation.Dynamics.PronyStateBounds
public import KVApproximation.Dynamics.PronyTrajectory
public import KVApproximation.Tensor.MandelBlockIsometry

/-!
# Uniform bounds for the material-dependent internal variables

Compactness bounds the Frobenius norms of the coefficient tensors. The
positive common rate then bounds the tensor states, and Mandel isometry
preserves the Euclidean sum when passing to scalar coordinates.
-/

public section

open MeasureTheory
open KVApproximation.Tensor KVApproximation.Approximation KVApproximation.Dynamics

namespace KVApproximation.KelvinVoigt

private theorem compact_prony_states {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {n d : ℕ} (P : PronyModel A (Symmetric d) n) (K : Fin n → A → Elasticity d)
    (hK : ∀ k, Continuous (K k)) (hcoef : ∀ k a, P.coefficient k a = actionL d (K k a))
    {βE βV δ lower : ℝ} (hβE : 0 < βE) (hβV : 0 < βV) (hδ : 0 < δ)
    (hlower : 0 < lower) (hrate : ∀ k, lower ≤ P.rate k) :
    ∃ δIV : ℝ, 0 < δIV ∧
      (⨆ a, ⨆ (e : BoundedTrajectory (Symmetric d)), ⨆ (_ : e.Admissible βE βV δ),
        eLpNorm (fun t => blockStrainMandel (P.state a e t)) ⊤ timeMeasure) ≤
          ENNReal.ofReal δIV := by
  classical
  choose C hC using fun k => isCompact_univ.exists_bound_of_continuousOn (hK k).continuousOn
  let D : Fin n → ℝ := fun k => max (C k) 0
  have hD (k : Fin n) : 0 ≤ D k := le_max_right _ _
  have hbound (k : Fin n) (a : A) : ‖P.coefficient k a‖ ≤ D k := by
    rw [hcoef]
    apply ContinuousLinearMap.opNorm_le_bound _ (hD k)
    intro e
    exact (norm_action_le (K k a) e).trans
      (mul_le_mul_of_nonneg_right ((hC k a (Set.mem_univ _)).trans (le_max_left _ _))
        (norm_nonneg e))
  let B := δ / (βV * lower) * Real.sqrt (∑ k : Fin n, D k ^ 2)
  have hB : 0 ≤ B := mul_nonneg
    (div_nonneg hδ.le (mul_nonneg hβV.le hlower.le)) (Real.sqrt_nonneg _)
  refine ⟨1 + B, by linarith, ?_⟩
  apply iSup_le
  intro a
  apply iSup_le
  intro e
  apply iSup_le
  intro he
  obtain ⟨q, hq, _⟩ := pronyState_isKineticSolution P
    (fun k => hlower.trans_le (hrate k)) a e
  obtain ⟨T, hT⟩ := blockStrainMandel_isometry n d
  have htime : ∀ᵐ t ∂timeMeasure, 0 ≤ t := ae_restrict_mem measurableSet_Ici
  have heq : (fun t => T (q.value t)) =ᵐ[timeMeasure]
      fun t => blockStrainMandel (P.state a e t) := by
    filter_upwards [htime] with t ht
    rw [hq t ht, hT]
  have hmap : AEStronglyMeasurable (fun t => T (q.value t)) timeMeasure :=
    T.continuous.comp_aestronglyMeasurable q.value_memLp.aestronglyMeasurable
  have hstrong := hmap.congr heq
  rw [eLpNorm_exponent_top hstrong]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [htime] with t ht
  rw [blockStrainMandel_norm]
  exact (prony_state_bound P a hβE hβV hδ.le hlower hrate D hD
    (fun k => hbound k a) e he ht).trans (by dsimp only [B]; linarith)

variable {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
variable {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
variable (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE) (hδ : 0 < δ)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hd hVorder hγV hEorder hγE hδ

/-- Lemma B.11 (`lem:ua_step3_targets`): all local Prony internal variables,
in the prescribed scalar Mandel coordinates, have one uniform L∞ bound
over the full half-line and the actual material and strain classes. -/
theorem local_prony_state_uniform_bound (hspan : αE / βV < βE / αV)
    {m : ℕ} (hm : 0 < m) :
    let P := localPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) m
    ∃ δIV : ℝ, 0 < δIV ∧
      (⨆ M, ⨆ (e : BoundedTrajectory (Symmetric d)), ⨆ (_ : e.Admissible βE βV δ),
        eLpNorm (fun t => blockStrainMandel (P.state M e t)) ⊤ timeMeasure) ≤
          ENNReal.ofReal δIV := by
  let : CompactSpace (admissibleMaterials d αV βV γV αE βE γE) :=
    isCompact_iff_compactSpace.mp
      (isCompact_admissibleMaterials hd hαV hVorder hγV hαE hEorder hγE)
  dsimp only
  refine compact_prony_states _
    (fun k M => localPronyCoefficient (S.measure M) (βE / βV) (αE / βV) (βE / αV) m
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (fun k => continuous_local_prony_coefficient hαV hVorder hαE hEorder C S hspan hm
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (fun _ _ => rfl) (hαE.trans_le hEorder) (hαV.trans_le hVorder) hδ
    (div_pos hαE (hαV.trans_le hVorder)) ?_
  intro k
  exact (localPronyRate_mem (div_pos hαE (hαV.trans_le hVorder)) hspan hm
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).1

/-- Lemma B.11, singleton spectral interval: the exact one-term model
has the same full-half-line uniform scalar-state bound. -/
theorem singleton_prony_state_uniform_bound (hspan : αE / βV = βE / αV) :
    let P := singletonPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (αE / βV)
    ∃ δIV : ℝ, 0 < δIV ∧
      (⨆ M, ⨆ (e : BoundedTrajectory (Symmetric d)), ⨆ (_ : e.Admissible βE βV δ),
        eLpNorm (fun t => blockStrainMandel (P.state M e t)) ⊤ timeMeasure) ≤
          ENNReal.ofReal δIV := by
  let : CompactSpace (admissibleMaterials d αV βV γV αE βE γE) :=
    isCompact_iff_compactSpace.mp
      (isCompact_admissibleMaterials hd hαV hVorder hγV hαE hEorder hγE)
  dsimp only
  exact compact_prony_states _ (fun _ M => singletonPronyCoefficient (S.measure M))
    (fun _ => continuous_singleton_prony_coefficient hαV hVorder hαE hEorder C S hspan)
    (fun _ _ => rfl) (hαE.trans_le hEorder) (hαV.trans_le hVorder) hδ
    (div_pos hαE (hαV.trans_le hVorder)) (fun _ => le_rfl)

end KVApproximation.KelvinVoigt
