module

public import KVApproximation.KelvinVoigt.ContinuousPronyApproximation
public import KVApproximation.KelvinVoigt.MaterialResponseContinuity
public import KVApproximation.KelvinVoigt.PronySingleton
public import KVApproximation.Approximation.PronyIdentities

/-!
# Neural responses for the local and singleton Prony models
-/

public section

open MeasureTheory
open KVApproximation.Dynamics
open KVApproximation.Tensor KVApproximation.Approximation
open KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

variable {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
variable {αV βV γV αE βE γE δ ε : ℝ}
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
variable (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE)
variable (hδ : 0 < δ) (hε : 0 < ε)
variable (C : CellFamily d αV βV γV αE βE γE hαV hαE) (S : SpectralFamily C)

include hd hVorder hγV hEorder hγE hδ hε S

/-- Theorem 4.4, completion of the proof in Appendix B.3
(`eq:ua_error_tolerances`): any strict uniform Prony error gap leaves
room for B.12–B.13 without adding scalar state coordinates. -/
theorem local_prony_neural_approximation (hspan : αE / βV < βE / αV)
    {m : ℕ} (hm : 0 < m)
    (herror : uniformPronyError C
      (localPronyModel S.measure (fun M => (C M).viscosity) (fun M => (C M).elasticity)
        (βE / βV) (αE / βV) (βE / αV) m) δ < ENNReal.ofReal ε) :
    let n := logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)) * m
    ∀ (Fclass : StressResponseClass d (n * strainDimension d))
      (Gclass : KineticResponseClass d (n * strainDimension d)),
      HasUniversalApproximation Fclass → HasLocallyLipschitzApproximation Gclass →
      ∃ F ∈ Fclass, ∃ G ∈ Gclass, UniformlyApproximates C F G δ ε := by
  dsimp only
  intro Fclass Gclass hF hG
  let P := localPronyModel S.measure (fun M => (C M).viscosity)
    (fun M => (C M).elasticity) (βE / βV) (αE / βV) (βE / αV) m
  have hlower : 0 < αE / βV := div_pos hαE (hαV.trans_le hVorder)
  have hn : 0 < logPartitionCount (logarithmicSpan (αE / βV) (βE / αV)) * m :=
    Nat.mul_pos (Nat.succ_pos _) hm
  exact continuous_prony_neural_approximation hd hαV hVorder hγV hαE hEorder hγE
    hδ hε C hn P
    ((actionL d).continuous.comp (continuous_cell_viscosity hαV hVorder hαE hEorder C))
    ((actionL d).continuous.comp (continuous_cell_elasticity hαV hVorder hαE hEorder C))
    (fun k => (actionL d).continuous.comp
      (continuous_local_prony_coefficient hαV hVorder hαE hEorder C S hspan hm
        (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
    hlower (fun k => (localPronyRate_mem hlower hspan hm
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).1)
    herror Fclass Gclass hF hG

/-- Theorems 4.4–4.5, singleton case: exact one-term Prony stress and
B.12–B.13 give neural approximation with one symmetric-tensor state. -/
theorem singleton_prony_neural_approximation (hspan : αE / βV = βE / αV) :
    ∀ (Fclass : StressResponseClass d (1 * strainDimension d))
      (Gclass : KineticResponseClass d (1 * strainDimension d)),
      HasUniversalApproximation Fclass → HasLocallyLipschitzApproximation Gclass →
      ∃ F ∈ Fclass, ∃ G ∈ Gclass, UniformlyApproximates C F G δ ε := by
  intro Fclass Gclass hF hG
  let P := singletonPronyModel S.measure (fun M => (C M).viscosity)
    (fun M => (C M).elasticity) (αE / βV)
  have hlower : 0 < αE / βV := div_pos hαE (hαV.trans_le hVorder)
  have hP : uniformPronyError C P δ ≤ ENNReal.ofReal (ε / 2) := by
    apply iSup_le
    intro M
    apply iSup_le
    intro e
    apply iSup_le
    intro _he
    have heq : (fun t => constitutiveStress (C M) e t - P.stress M e t) =ᵐ[timeMeasure]
        fun _ => 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [singleton_prony_exact hαV hVorder hαE hEorder C S hspan M e ht]
      exact sub_self _
    rw [eLpNorm_congr_ae heq]
    change eLpNorm (0 : ℝ → Symmetric d) ⊤ timeMeasure ≤ _
    exact (eLpNorm_zero (α := ℝ) (ε := Symmetric d) (p := ⊤) (μ := timeMeasure)).le.trans
      zero_le
  have herror : uniformPronyError C P δ < ENNReal.ofReal ε :=
    hP.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))
  exact continuous_prony_neural_approximation hd hαV hVorder hγV hαE hEorder hγE
    hδ hε C (by decide : 0 < 1) P
    ((actionL d).continuous.comp (continuous_cell_viscosity hαV hVorder hαE hEorder C))
    ((actionL d).continuous.comp (continuous_cell_elasticity hαV hVorder hαE hEorder C))
    (fun _ => (actionL d).continuous.comp
      (continuous_singleton_prony_coefficient hαV hVorder hαE hEorder C S hspan))
    hlower (fun _ => le_rfl) herror Fclass Gclass hF hG

end KVApproximation.KelvinVoigt
