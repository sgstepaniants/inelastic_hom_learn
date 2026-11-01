module

public import KVApproximation.NeuralOperators.CoordinateClasses
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Approximation properties under coordinate transport
-/

public section

namespace KVApproximation.NeuralOperators

variable {X X' M M' F F' : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace X']
  [TopologicalSpace M] [TopologicalSpace M']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- Lemma B.12: compact-image transport and output isometry preserve A1
with the same approximation tolerance. -/
theorem HasUniversalApproximation.inducedResponseClass
    (S : X ≃ᵢ X') (U : M ≃ₜ M') (T : F ≃ₗᵢ[ℝ] F')
    {N : Set C(X' × M', F')} (hN : HasUniversalApproximation N) :
    HasUniversalApproximation (inducedResponseClass S U T N) := by
  intro K L hK hL g ε hε
  let S' := S.toHomeomorph.image K
  let U' := U.image L
  let g' : C((S '' K) × (U '' L), F') :=
    ⟨fun z => T (g (S'.symm z.1, U'.symm z.2)),
      T.continuous.comp (g.continuous.comp
        ((S'.symm.continuous.comp continuous_fst).prodMk
          (U'.symm.continuous.comp continuous_snd)))⟩
  obtain ⟨Φ, hΦ, hbound⟩ := hN _ _ (hK.image S.continuous) (hL.image U.continuous) g' ε hε
  refine ⟨inducedResponse S U T Φ, ⟨Φ, hΦ, rfl⟩, ?_⟩
  intro x m
  have hb := hbound (S' x) (U' m)
  change ‖T.symm (Φ (S x.val, U m.val)) - g (x, m)‖ ≤ ε
  rw [← T.norm_map (T.symm (Φ (S x.val, U m.val)) - g (x, m)),
    map_sub, T.apply_symm_apply]
  simp only [g', ContinuousMap.coe_mk, Homeomorph.symm_apply_apply] at hb
  have hSx : (S' x).val = S x.val :=
    (Homeomorph.image_apply_coe S.toHomeomorph K x).trans
      (congrFun (IsometryEquiv.coe_toHomeomorph S) x.val)
  have hUm : (U' m).val = U m.val := Homeomorph.image_apply_coe U L m
  rwa [hSx, hUm] at hb

/-- Lemma B.12: the same compact-image construction preserves A2,
including local Lipschitz regularity in the full vector input. -/
theorem HasLocallyLipschitzApproximation.inducedResponseClass
    (S : X ≃ᵢ X') (U : M ≃ₜ M') (T : F ≃ₗᵢ[ℝ] F')
    {N : Set C(X' × M', F')} (hN : HasLocallyLipschitzApproximation N) :
    HasLocallyLipschitzApproximation (inducedResponseClass S U T N) := by
  intro K L hK hL g ε hε
  let S' := S.toHomeomorph.image K
  let U' := U.image L
  let g' : C((S '' K) × (U '' L), F') :=
    ⟨fun z => T (g (S'.symm z.1, U'.symm z.2)),
      T.continuous.comp (g.continuous.comp
        ((S'.symm.continuous.comp continuous_fst).prodMk
          (U'.symm.continuous.comp continuous_snd)))⟩
  obtain ⟨Φ, hΦ, hbound, hlip⟩ :=
    hN _ _ (hK.image S.continuous) (hL.image U.continuous) g' ε hε
  refine ⟨inducedResponse S U T Φ, ⟨Φ, hΦ, rfl⟩, ?_, ?_⟩
  · intro x m
    have hb := hbound (S' x) (U' m)
    change ‖T.symm (Φ (S x.val, U m.val)) - g (x, m)‖ ≤ ε
    rw [← T.norm_map (T.symm (Φ (S x.val, U m.val)) - g (x, m)),
      map_sub, T.apply_symm_apply]
    simp only [g', ContinuousMap.coe_mk, Homeomorph.symm_apply_apply] at hb
    have hSx : (S' x).val = S x.val :=
      (Homeomorph.image_apply_coe S.toHomeomorph K x).trans
        (congrFun (IsometryEquiv.coe_toHomeomorph S) x.val)
    have hUm : (U' m).val = U m.val := Homeomorph.image_apply_coe U L m
    rwa [hSx, hUm] at hb
  · intro m hm
    exact T.symm.lipschitzWith.locallyLipschitz.comp
      ((hlip (U m) ⟨m, hm, rfl⟩).comp S.isometry.lipschitzWith.locallyLipschitz)

end KVApproximation.NeuralOperators
