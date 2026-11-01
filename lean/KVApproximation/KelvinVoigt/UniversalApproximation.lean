import KVApproximation.KelvinVoigt.ApproximationProblem
import KVApproximation.Approximation.LogPartition
import KVApproximation.Approximation.DimensionEstimates
import KVApproximation.KelvinVoigt.PronyNeuralApproximation
import KVApproximation.KelvinVoigt.PronyError
import KVApproximation.KelvinVoigt.SpectralRepresentation
import KVApproximation.Homogenization.CellConstitutive

/-!
# Uniform approximation and sufficient state dimension
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

/-- Theorem 4.5 (`thm:sufficient_dimension`): the exact sufficient scalar
state dimension, with a separate singleton case. The logarithmic span uses
the common spectral interval; the relative error is `ε / δ`. -/
theorem sufficient_internal_variable_dimension :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε →
        let N := sufficientDimension d
          (Approximation.logarithmicSpan (αE / βV) (βE / αV)) (ε / δ)
        ∃ F ∈ Fclass N, ∃ G ∈ Gclass N,
          UniformlyApproximates C F G δ ε := by
  classical
  have hβV : 0 < βV := hαV.trans_le hVorder
  have hβE : 0 < βE := hαE.trans_le hEorder
  have hdset : d ∈ ({1, 2, 3} : Set ℕ) := by
    rcases hd with rfl | rfl | rfl <;> simp
  have hdpos : 0 < d := by rcases hd with rfl | rfl | rfl <;> decide
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
    have hN : sufficientDimension d (logarithmicSpan (αE / βV) (βE / αV)) (ε / δ) =
        1 * strainDimension d := by
      rw [sufficientDimension, ite_eq_left hR, one_mul]
    rw [hN]
    exact singleton_prony_neural_approximation hdset hαV hVorder hγV hαE hEorder hγE hδ hε
      C S hspan (Fclass _) (Gclass _) (hF _) (hG _)
  · have hspanlt : αE / βV < βE / αV := lt_of_le_of_ne horder hspan
    have hR : 0 < logarithmicSpan (αE / βV) (βE / αV) :=
      Real.log_pos ((one_lt_div hlower).mpr hspanlt)
    let m := interpolationOrder (pronyConstant (strainDimension d) 1) (ε / δ)
    have hm : 0 < m := interpolationOrder_pos _ _
    have hcos : 0 < Real.cos (3 / 4 : ℝ) := by linarith [cos_three_quarters_lower]
    have hκ : 0 ≤ pronyConstant (strainDimension d) 1 := by
      dsimp [pronyConstant, ellipseResponseFactor]
      positivity
    have hgeom : pronyErrorBound (strainDimension d) δ m ≤ ε := by
      have h := interpolationOrder_error_le hκ (div_pos hε hδ)
      have heq : pronyErrorBound (strainDimension d) δ m =
          δ * (pronyConstant (strainDimension d) 1 / (2 : ℝ) ^ (m - 1)) := by
        unfold pronyErrorBound pronyConstant
        ring
      rw [heq]
      calc
        _ ≤ δ * (ε / δ) := mul_le_mul_of_nonneg_left h hδ.le
        _ = ε := by field_simp
    have herror := (local_prony_error_lt hαV hVorder hαE hEorder C S
      hdpos hδ hspanlt hm).trans_le (ENNReal.ofReal_le_ofReal hgeom)
    have hN : sufficientDimension d (logarithmicSpan (αE / βV) (βE / αV)) (ε / δ) =
        (logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)) * m) * strainDimension d := by
      rw [sufficientDimension, ite_eq_right hR.ne']
      dsimp only [nonsingletonStateDimension, m]
      ac_rfl
    rw [hN]
    exact local_prony_neural_approximation hdset hαV hVorder hγV hαE hEorder hγE
      hδ hε C S hspanlt hm herror (Fclass _) (Gclass _) (hF _) (hG _)

/-- Theorem 4.4 (`thm:ua`): uniform approximation over the actual material
and strain classes on the whole nonnegative time axis. The cell family is
fixed before the error tolerance and is defined by the periodic cell forms.
The tensor inputs are identified with the paper's vector inputs by Mandel
isometries. No nonemptiness assumption is imposed on the material class. -/
theorem universal_approximation :
    ∃ C : CellFamily d αV βV γV αE βE γE hαV hαE,
      ∀ ε : ℝ, 0 < ε → ∃ nξ : ℕ,
        ∃ F ∈ Fclass nξ, ∃ G ∈ Gclass nξ,
          UniformlyApproximates C F G δ ε := by
  obtain ⟨C, hC⟩ := sufficient_internal_variable_dimension hd hαV hVorder hγV
    hαE hEorder hγE hδ Fclass Gclass hF hG
  refine ⟨C, ?_⟩
  intro ε hε
  exact ⟨sufficientDimension d (logarithmicSpan (αE / βV) (βE / αV)) (ε / δ), hC ε hε⟩

end KVApproximation.KelvinVoigt
