import KVApproximation.Approximation.AlternativeDimensionEstimates
import KVApproximation.KelvinVoigt.PronyNeuralApproximation
import KVApproximation.KelvinVoigt.AlternativePronyContinuity
import KVApproximation.KelvinVoigt.SpectralRepresentation
import KVApproximation.Homogenization.CellConstitutive
import KVApproximation.KelvinVoigt.GlobalPronyError
import KVApproximation.Approximation.GlobalRates
import KVApproximation.Approximation.ChebyshevNodes

/-!
# Neural approximation with one global logarithmic interpolant
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

/-- Remark 4.6, global weighted construction: the second alternative
establishes Theorem 4.4 at its stated sufficient dimension, with every
positive logarithmic span and the separate exact singleton case. -/
theorem global_sufficient_internal_variable_dimension :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε →
        let R := logarithmicSpan (αE / βV) (βE / αV)
        let N := if R = 0 then strainDimension d else
          globalPronyDimension (strainDimension d) R (ε / δ)
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
    have hdpos : 0 < d := by rcases hd with rfl | rfl | rfl <;> decide
    have hdim : 0 < strainDimension d := by
      unfold strainDimension
      exact Nat.div_pos (by nlinarith) (by decide)
    let R := logarithmicSpan (αE / βV) (βE / αV)
    let n := globalInterpolationOrder (strainDimension d) R (ε / δ)
    have hn : 0 < n := by dsimp [n, globalInterpolationOrder]; omega
    let P := globalPronyModel S.measure (fun M => (C M).viscosity)
      (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) n
    have hgeom : globalPronyErrorBound (strainDimension d) δ R n ≤ ε := by
      have h := globalInterpolationOrder_error_le_of_span_pos hdim hR (div_pos hε hδ)
      have heq : globalPronyErrorBound (strainDimension d) δ R n =
          δ * globalPronyErrorBound (strainDimension d) 1 R n := by
        unfold globalPronyErrorBound pronyConstant
        ring
      rw [heq]
      calc
        _ ≤ δ * (ε / δ) := mul_le_mul_of_nonneg_left h hδ.le
        _ = ε := by field_simp
    have herror : uniformPronyError C P δ < ENNReal.ofReal ε :=
      (global_prony_error_lt_of_span_pos hαV hVorder hαE hEorder C S hdpos hδ hR hn).trans_le
        (ENNReal.ofReal_le_ofReal hgeom)
    have hN : globalPronyDimension (strainDimension d) R (ε / δ) = n * strainDimension d := by
      dsimp only [globalPronyDimension, n]
      exact Nat.mul_comm _ _
    rw [show globalPronyDimension (strainDimension d)
      (logarithmicSpan (αE / βV) (βE / αV)) (ε / δ) = n * strainDimension d from hN]
    exact continuous_prony_neural_approximation hdset hαV hVorder hγV hαE hEorder hγE
      hδ hε C hn P
      ((actionL d).continuous.comp (continuous_cell_viscosity hαV hVorder hαE hEorder C))
      ((actionL d).continuous.comp (continuous_cell_elasticity hαV hVorder hαE hEorder C))
      (fun k => (actionL d).continuous.comp
        (continuous_globalPronyCoefficient hαV hVorder hαE hEorder C S n k))
      hlower (fun k => (globalLogRate_mem hlower horder (chebyshevNode_mem n k)).1)
      herror (Fclass _) (Gclass _) (hF _) (hG _)

end KVApproximation.KelvinVoigt
