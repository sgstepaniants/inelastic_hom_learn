module

public import KVApproximation.NeuralOperators.ResponseDomains
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Approximation of the Prony response maps

The compact input constraints and continuous material coefficients give
continuous targets on the two compact products. Assumptions A1 and A2
then supply the stress and kinetic approximators simultaneously.
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem continuous_pronyStress_restrict {n : ℕ} (P : PronyModel M E n)
    (K : Set (StressInput E (BlockState n E))) (L : Set M)
    (hV : ContinuousOn P.viscosity L) (hE : ContinuousOn P.elasticity L) :
    Continuous (fun z : K × L => pronyStressResponse P z.2.val z.1.val) := by
  have hx := (WithLp.prod_continuous_ofLp 2 E (WithLp 2 (E × BlockState n E))).comp
    (continuous_subtype_val.comp (continuous_fst (X := K) (Y := L)))
  have hy := (WithLp.prod_continuous_ofLp 2 E (BlockState n E)).comp hx.snd
  have hV' : Continuous (fun z : K × L => P.viscosity z.2.val) :=
    (continuousOn_iff_continuous_domRestrict.mp hV).comp continuous_snd
  have hE' : Continuous (fun z : K × L => P.elasticity z.2.val) :=
    (continuousOn_iff_continuous_domRestrict.mp hE).comp continuous_snd
  have hs : Continuous (fun z : K × L =>
      ∑ k : Fin n, (WithLp.ofLp (WithLp.ofLp z.1.val).2).2 k) :=
    continuous_finsetSum _ (fun k _ =>
      (PiLp.continuous_apply 2 (fun _ : Fin n => E) k).comp hy.snd)
  exact ((hV'.clm_apply hy.fst).add (hE'.clm_apply hx.fst)).add hs

omit [FiniteDimensional ℝ E] in
private theorem continuous_pronyKinetic_restrict {n : ℕ} (P : PronyModel M E n)
    (K : Set (KineticInput E (BlockState n E))) (L : Set M)
    (hcoef : ∀ k, ContinuousOn (P.coefficient k) L) :
    Continuous (fun z : K × L => pronyKineticResponse P z.2.val z.1.val) := by
  have hx := (WithLp.prod_continuous_ofLp 2 E (BlockState n E)).comp
    (continuous_subtype_val.comp (continuous_fst (X := K) (Y := L)))
  change Continuous (fun z : K × L => WithLp.toLp 2 (fun k =>
    P.coefficient k z.2.val (WithLp.ofLp z.1.val).1 -
      P.rate k • (WithLp.ofLp z.1.val).2 k))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => E)).comp
  apply continuous_pi
  intro k
  have hk : Continuous (fun z : K × L => P.coefficient k z.2.val) :=
    (continuousOn_iff_continuous_domRestrict.mp (hcoef k)).comp continuous_snd
  exact (hk.clm_apply hx.fst).sub
    (((PiLp.continuous_apply 2 (fun _ : Fin n => E) k).comp hx.snd).const_smul (P.rate k))

/-- Lemma B.12 (`lem:ua_step3_no`): simultaneous approximation of both
responses on the prescribed compact domains, with local Lipschitz regularity
for the full kinetic vector input at each material. Mandel transport converts
the block state to the scalar state of dimension `n * dim E`. -/
theorem prony_responses_approximate {n : ℕ} (P : PronyModel M E n)
    (L : Set M) (hL : IsCompact L)
    (hV : ContinuousOn P.viscosity L) (hE : ContinuousOn P.elasticity L)
    (hcoef : ∀ k, ContinuousOn (P.coefficient k) L)
    {βE βV δ radius εF εG : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (_hδ : 0 < δ) (_hRadius : 0 < radius)
    (hεF : 0 < εF) (hεG : 0 < εG)
    (Fclass : Set C(StressInput E (BlockState n E) × M, E))
    (Gclass : Set C(KineticInput E (BlockState n E) × M, BlockState n E))
    (hF : HasUniversalApproximation Fclass) (hG : HasLocallyLipschitzApproximation Gclass) :
    ∃ F ∈ Fclass, ∃ G ∈ Gclass,
      (∀ a ∈ L, ∀ x ∈ stressInputSet (E := E) (Q := BlockState n E) βE βV δ radius,
        ‖F (x, a) - pronyStressResponse P a x‖ ≤ εF) ∧
      (∀ a ∈ L, ∀ x ∈ kineticInputSet (E := E) (Q := BlockState n E) βV δ radius,
        ‖G (x, a) - pronyKineticResponse P a x‖ ≤ εG) ∧
      ∀ a ∈ L, LocallyLipschitz (fun x => G (x, a)) := by
  let KF := stressInputSet (E := E) (Q := BlockState n E) βE βV δ radius
  let KG := kineticInputSet (E := E) (Q := BlockState n E) βV δ radius
  let f : C(KF × L, E) :=
    ⟨fun z => pronyStressResponse P z.2.val z.1.val,
      continuous_pronyStress_restrict P KF L hV hE⟩
  let g : C(KG × L, BlockState n E) :=
    ⟨fun z => pronyKineticResponse P z.2.val z.1.val,
      continuous_pronyKinetic_restrict P KG L hcoef⟩
  obtain ⟨F, hFmem, hFbound⟩ := hF KF L (isCompact_stressInputSet hβE hβV δ radius)
    hL f εF hεF
  obtain ⟨G, hGmem, hGbound, hGlip⟩ := hG KG L (isCompact_kineticInputSet hβV δ radius)
    hL g εG hεG
  exact ⟨F, hFmem, G, hGmem,
    (fun a ha x hx => hFbound ⟨x, hx⟩ ⟨a, ha⟩),
    (fun a ha x hx => hGbound ⟨x, hx⟩ ⟨a, ha⟩), hGlip⟩

end KVApproximation.NeuralOperators
