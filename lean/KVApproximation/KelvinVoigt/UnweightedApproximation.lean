import KVApproximation.Approximation.AlternativeDimensionEstimates
import KVApproximation.KelvinVoigt.PronyNeuralApproximation
import KVApproximation.KelvinVoigt.AlternativePronyContinuity
import KVApproximation.KelvinVoigt.SpectralRepresentation
import KVApproximation.Homogenization.CellConstitutive
import KVApproximation.KelvinVoigt.UnweightedPronyError
import KVApproximation.Approximation.PronyIdentities

/-!
# Neural approximation with unweighted local interpolation
-/

open KVApproximation.Tensor KVApproximation.NeuralOperators
open KVApproximation.Approximation KVApproximation.Spectral KVApproximation.Homogenization

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} (hd : d = 1 ∨ d = 2 ∨ d = 3)
variable {αV βV γV αE βE γE δ : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
variable (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE) (hδ : 0 < δ)
variable (Fclass : ∀ nξ : ℕ, StressResponseClass d nξ)
variable (Gclass : ∀ nξ : ℕ, KineticResponseClass d nξ)
variable (hF : ∀ nξ, HasUniversalApproximation (Fclass nξ))
variable (hG : ∀ nξ, HasLocallyLipschitzApproximation (Gclass nξ))

include hd hVorder hγV hEorder hγE hδ hF hG

/-- Remark 4.6, unweighted construction: the first alternative establishes
Theorem 4.4 at its stated sufficient dimension. The singleton case uses
one symmetric-tensor state; the cell family is fixed before the tolerance. -/
theorem unweighted_sufficient_internal_variable_dimension :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε →
        let R := logarithmicSpan (αE / βV) (βE / αV)
        let N := if R = 0 then strainDimension d else
          unweightedDimension (strainDimension d) R (ε / δ) (βE / αE)
        ∃ F ∈ Fclass N, ∃ G ∈ Gclass N,
          UniformlyApproximates C F G δ ε := by
  classical
  have hβV : 0 < βV := hαV.trans_le hVorder
  have hβE : 0 < βE := hαE.trans_le hEorder
  have hdset : d ∈ ({1, 2, 3} : Set ℕ) := by
    rcases hd with rfl | rfl | rfl <;> simp
  let C : CellFamily d αV βV γV αE βE γE hαV hαE := fun M =>
    (cellConstitutiveModel_exists_unique (materialViscosity hαV M)
      (materialElasticity hαE M)).choose
  have hex (M : admissibleMaterials d αV βV γV αE βE γE) :
      ∃ ν, IsSpectralRepresentation ν (C M).kernel (αE / βV) (βE / αV) := by
    obtain ⟨ν, hp, hs, hvar, hk⟩ := spectral_representation
      (materialViscosity hαV M) (materialElasticity hαE M) (C M)
      hαV hβV hαE hβE (materialViscosity hαV M).bounds (materialElasticity hαE M).bounds
    exact ⟨ν, hp, hs, hvar.trans_lt ENNReal.ofReal_lt_top, hk⟩
  choose ν hν using hex
  let S : SpectralFamily C := ⟨ν, hν⟩
  refine ⟨C, ?_⟩
  intro ε hε
  dsimp only
  have hlower : 0 < αE / βV := div_pos hαE hβV
  have horder : αE / βV ≤ βE / αV :=
    (div_le_div_of_nonneg_right hEorder hβV.le).trans
      (div_le_div_of_nonneg_left hβE.le hαV hVorder)
  by_cases hspan : αE / βV = βE / αV
  · have hR : logarithmicSpan (αE / βV) (βE / αV) = 0 := by
      simp [logarithmicSpan, ← hspan, div_self hlower.ne']
    rw [ite_eq_left hR, ← Nat.one_mul (strainDimension d)]
    exact singleton_prony_neural_approximation hdset hαV hVorder hγV hαE hEorder hγE hδ hε
        C S hspan (Fclass _) (Gclass _) (hF _) (hG _)
  · have hspanlt : αE / βV < βE / αV := lt_of_le_of_ne horder hspan
    have hR : 0 < logarithmicSpan (αE / βV) (βE / αV) :=
      Real.log_pos ((one_lt_div hlower).mpr hspanlt)
    rw [ite_eq_right hR.ne']
    let m := interpolationOrder
      (2 * unweightedErrorConstant (strainDimension d) 1 (βE / αE)) (ε / δ)
    have hm : 0 < m := interpolationOrder_pos _ _
    let P := unweightedLocalModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (αE / βV) (βE / αV) m
    have hcos : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
    have hU : 0 ≤ unweightedErrorConstant (strainDimension d) 1 (βE / αE) := by
      dsimp [unweightedErrorConstant]
      positivity
    have hgeom : unweightedErrorConstant (strainDimension d) δ (βE / αE) /
        (2 : ℝ) ^ (m - 1) ≤ ε / 2 := by
      have h := unweighted_order_error_le hU (div_pos hε hδ)
      have heq : unweightedErrorConstant (strainDimension d) δ (βE / αE) /
          (2 : ℝ) ^ (m - 1) = δ *
          (unweightedErrorConstant (strainDimension d) 1 (βE / αE) / (2 : ℝ) ^ (m - 1)) := by
        unfold unweightedErrorConstant
        ring
      rw [heq]
      calc
        _ ≤ δ * ((ε / δ) / 2) := mul_le_mul_of_nonneg_left h hδ.le
        _ = ε / 2 := by field_simp
    have herror : uniformPronyError C P δ < ENNReal.ofReal ε :=
      ((unweighted_prony_error_le hαV hVorder hαE hEorder C S hδ hspanlt hm).trans
        (ENNReal.ofReal_le_ofReal hgeom)).trans_lt
          ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))
    have hN : unweightedDimension (strainDimension d)
        (logarithmicSpan (αE / βV) (βE / αV)) (ε / δ) (βE / αE) =
          (logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)) * m) * strainDimension d := by
      dsimp only [unweightedDimension, m]
      ac_rfl
    rw [hN]
    exact continuous_prony_neural_approximation hdset hαV hVorder hγV hαE hEorder hγE
      hδ hε C (Nat.mul_pos (Nat.succ_pos _) hm) P
      ((actionL d).continuous.comp (continuous_cell_viscosity hαV hVorder hαE hEorder C))
      ((actionL d).continuous.comp (continuous_cell_elasticity hαV hVorder hαE hEorder C))
      (fun k => (actionL d).continuous.comp
        (continuous_unweightedLocalCoefficient hαV hVorder hαE hEorder C S m
          (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
      hlower (fun k => (localPronyRate_mem hlower hspanlt hm
        (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).1)
      herror (Fclass _) (Gclass _) (hF _) (hG _)

end KVApproximation.KelvinVoigt
