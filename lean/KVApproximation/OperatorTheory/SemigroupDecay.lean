module

public import KVApproximation.OperatorTheory.MemoryIdentities
public import KVApproximation.OperatorTheory.SpectralBounds
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Exponential decay in the viscous energy

Section 3.2 bounds the relaxation spectrum below by `αE / βV`. Applying
the decreasing exponential through the continuous functional calculus bounds
the squared semigroup, and hence the energy, by the corresponding scalar decay.
-/

public section

open scoped InnerProductSpace

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Section 3.2: the positive spectral lower bound gives exponential energy decay. -/
theorem relaxationSemigroup_energy_le (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) {αV βV αE βE : ℝ} (hβV : 0 < βV) (hαE : 0 < αE)
    (hV : V.HasBounds αV βV) (hE : E.HasBounds αE βE) (t : ℝ) (ht : 0 ≤ t) (u : X) :
    V.form (relaxationSemigroup V E X t u) (relaxationSemigroup V E X t u) ≤
      Real.exp (-2 * (αE / βV) * t) * V.form u u := by
  let R := weightedRelaxation V E X
  have hR : IsSelfAdjoint R := weightedRelaxation_isSelfAdjoint V E X
  have hlo : ∀ r ∈ spectrum ℝ R, αE / βV ≤ r :=
    (algebraMap_le_iff_le_spectrum hR).mp
      (weightedRelaxation_lower_bound V E X hβV hαE hV hE)
  have hfc : ContinuousOn (fun r : ℝ => Real.exp (-(2 * t) * r)) (spectrum ℝ R) := by
    fun_prop
  have hb : cfc (fun r : ℝ => Real.exp (-(2 * t) * r)) R ≤
      algebraMap ℝ _ (Real.exp (-2 * (αE / βV) * t)) := by
    apply (cfc_le_algebraMap_iff _ _ R hfc hR).mpr
    intro r hr
    apply Real.exp_le_exp.mpr
    calc
      -(2 * t) * r ≤ -(2 * t) * (αE / βV) :=
        mul_le_mul_of_nonpos_left (hlo r hr) (neg_nonpos.mpr (mul_nonneg (by norm_num) ht))
      _ = -2 * (αE / βV) * t := by ring
  have hcfc : cfc (fun r : ℝ => Real.exp (-(2 * t) * r)) R =
      NormedSpace.exp (-(2 * t) • R) := by
    rw [cfc_comp_const_mul _ Real.exp R Real.continuous_exp.continuousOn hR,
      CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all _).smul hR)]
  rw [hcfc] at hb
  change NormedSpace.exp (-(2 * t) • weightedRelaxation V E X) ≤ _ at hb
  rw [← relaxationSemigroup_conjugate V E X (2 * t)] at hb
  have hp := (ContinuousLinearMap.le_def.mp hb).inner_nonneg_left (WeightedSpace.mk u)
  have halg (r : ℝ) (w : RelaxationSpace V X) :
      algebraMap ℝ (RelaxationSpace V X →L[ℝ] RelaxationSpace V X) r w = r • w := rfl
  simp only [sub_apply, inner_sub_left, halg] at hp
  rw [real_inner_smul_left (WeightedSpace.mk u) (WeightedSpace.mk u)
    (Real.exp (-2 * (αE / βV) * t))] at hp
  -- The conjugated operator acts on the same vectors with the viscous pairing.
  change 0 ≤ Real.exp (-2 * (αE / βV) * t) * V.form u u -
    V.form (relaxationSemigroup V E X (2 * t) u) u at hp
  have htime : 2 * t = t + t := by ring
  rw [htime, relaxationSemigroup_add] at hp
  change 0 ≤ Real.exp (-2 * (αE / βV) * t) * V.form u u -
    V.form (relaxationSemigroup V E X t (relaxationSemigroup V E X t u)) u at hp
  rw [relaxationSemigroup_selfAdjoint] at hp
  exact sub_nonneg.mp hp

end KVApproximation.OperatorTheory
