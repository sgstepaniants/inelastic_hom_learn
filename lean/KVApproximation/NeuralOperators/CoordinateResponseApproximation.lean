module

public import KVApproximation.NeuralOperators.StateCoordinates
public import KVApproximation.NeuralOperators.ResponseDomains
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Response approximation on a compact material class
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.NeuralOperators

private theorem continuous_coordinateStress {M E Q : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {n : ℕ} (P : PronyModel M E n) (T : BlockState n E ≃ₗᵢ[ℝ] Q)
    (hV : Continuous P.viscosity) (hE : Continuous P.elasticity)
    (K : Set (StressInput E Q)) :
    Continuous (fun z : K × M => coordinateStressResponse P T z.2 z.1.val) := by
  have hu := (stressStateCoordinates (E := E) T).symm.continuous.comp
    (continuous_subtype_val.comp (continuous_fst (X := K) (Y := M)))
  have hx := (WithLp.prod_continuous_ofLp 2 E (WithLp 2 (E × BlockState n E))).comp hu
  have hy := (WithLp.prod_continuous_ofLp 2 E (BlockState n E)).comp hx.snd
  have hs : Continuous (fun z : K × M => ∑ k : Fin n,
      (WithLp.ofLp (WithLp.ofLp ((stressStateCoordinates T).symm z.1.val)).2).2 k) :=
    continuous_finsetSum _ (fun k _ =>
      (PiLp.continuous_apply 2 (fun _ : Fin n => E) k).comp hy.snd)
  exact (((hV.comp continuous_snd).clm_apply hy.fst).add
    ((hE.comp continuous_snd).clm_apply hx.fst)).add hs

private theorem continuous_coordinateKinetic {M E Q : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {n : ℕ} (P : PronyModel M E n) (T : BlockState n E ≃ₗᵢ[ℝ] Q)
    (hcoef : ∀ k, Continuous (P.coefficient k)) (K : Set (KineticInput E Q)) :
    Continuous (fun z : K × M => coordinateKineticResponse P T z.2 z.1.val) := by
  have hu := (kineticStateCoordinates (E := E) T).symm.continuous.comp
    (continuous_subtype_val.comp (continuous_fst (X := K) (Y := M)))
  have hx := (WithLp.prod_continuous_ofLp 2 E (BlockState n E)).comp hu
  apply T.continuous.comp
  change Continuous (fun z : K × M => WithLp.toLp 2 (fun k =>
    P.coefficient k z.2 (WithLp.ofLp ((kineticStateCoordinates T).symm z.1.val)).1 -
      P.rate k • (WithLp.ofLp ((kineticStateCoordinates T).symm z.1.val)).2 k))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => E)).comp
  apply continuous_pi
  intro k
  exact (((hcoef k).comp continuous_snd).clm_apply hx.fst).sub
    (((PiLp.continuous_apply 2 (fun _ : Fin n => E) k).comp hx.snd).const_smul (P.rate k))

/-- Lemma B.12: response mappings on the ambient material space approximate
a Prony model defined on its compact material class, in any isometric state
coordinates. A2 retains local Lipschitz regularity in the full kinetic input. -/
theorem prony_responses_approximate_in_coordinates
    {M E Q : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    (L : Set M) (hL : IsCompact L) {n : ℕ} (P : PronyModel L E n)
    (T : BlockState n E ≃ₗᵢ[ℝ] Q)
    (hV : Continuous P.viscosity) (hE : Continuous P.elasticity)
    (hcoef : ∀ k, Continuous (P.coefficient k))
    {βE βV δ radius εF εG : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (_hδ : 0 < δ) (_hRadius : 0 < radius)
    (hεF : 0 < εF) (hεG : 0 < εG)
    (Fclass : Set C(StressInput E Q × M, E))
    (Gclass : Set C(KineticInput E Q × M, Q))
    (hF : HasUniversalApproximation Fclass) (hG : HasLocallyLipschitzApproximation Gclass) :
    ∃ F ∈ Fclass, ∃ G ∈ Gclass,
      (∀ a : L, ∀ x ∈ stressInputSet (E := E) (Q := Q) βE βV δ radius,
        ‖F (x, a.val) - coordinateStressResponse P T a x‖ ≤ εF) ∧
      (∀ a : L, ∀ x ∈ kineticInputSet (E := E) (Q := Q) βV δ radius,
        ‖G (x, a.val) - coordinateKineticResponse P T a x‖ ≤ εG) ∧
      ∀ a : L, LocallyLipschitz (fun x => G (x, a.val)) := by
  let KF := stressInputSet (E := E) (Q := Q) βE βV δ radius
  let KG := kineticInputSet (E := E) (Q := Q) βV δ radius
  let f : C(KF × L, E) :=
    ⟨fun z => coordinateStressResponse P T z.2 z.1.val,
      continuous_coordinateStress P T hV hE KF⟩
  let g : C(KG × L, Q) :=
    ⟨fun z => coordinateKineticResponse P T z.2 z.1.val,
      continuous_coordinateKinetic P T hcoef KG⟩
  obtain ⟨F, hFmem, hFbound⟩ := hF KF L (isCompact_stressInputSet hβE hβV δ radius)
    hL f εF hεF
  obtain ⟨G, hGmem, hGbound, hGlip⟩ := hG KG L (isCompact_kineticInputSet hβV δ radius)
    hL g εG hεG
  exact ⟨F, hFmem, G, hGmem,
    (fun a x hx => hFbound ⟨x, hx⟩ a), (fun a x hx => hGbound ⟨x, hx⟩ a),
    (fun a => hGlip a.val a.property)⟩

end KVApproximation.NeuralOperators
