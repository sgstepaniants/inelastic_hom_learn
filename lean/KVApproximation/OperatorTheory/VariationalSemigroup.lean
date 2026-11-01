module

public import KVApproximation.OperatorTheory.CoerciveSolverProperties
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniform bounds for variational semigroups

The viscous energy decreases along homogeneous evolution. Norm equivalence
then gives a bound on the whole nonnegative time axis.
-/

public section

namespace KVApproximation.OperatorTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, homogeneous microscopic evolution: the relative Riesz
semigroup has the actual Hilbert-valued time derivative. -/
theorem relativeSemigroup_hasDerivAt (V E : CoerciveForm H) (u : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (-s • relativeRiesz V E)) u)
      (-relativeRiesz V E ((NormedSpace.exp (-t • relativeRiesz V E)) u)) t := by
  let : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
  have h := (hasDerivAt_exp_smul_const' (-relativeRiesz V E) t).clm_apply
    (hasDerivAt_const t u)
  simpa only [smul_neg, neg_smul, mul_apply_eq_comp,
    neg_apply, map_zero, add_zero] using h

/-- Theorem 3.1, uniform half-line estimate: homogeneous evolution
does not increase the viscous energy. -/
theorem relativeSemigroup_energy_le (V E : CoerciveForm H)
    (u : H) (t : ℝ) (ht : 0 ≤ t) :
    V.form ((NormedSpace.exp (-t • relativeRiesz V E)) u)
        ((NormedSpace.exp (-t • relativeRiesz V E)) u) ≤ V.form u u := by
  let q : ℝ → H := fun s => (NormedSpace.exp (-s • relativeRiesz V E)) u
  have hq (s : ℝ) : HasDerivAt q (-relativeRiesz V E (q s)) s :=
    relativeSemigroup_hasDerivAt V E u s
  have henergy (s : ℝ) : HasDerivAt (fun r => V.form (q r) (q r))
      (-2 * E.form (q s) (q s)) s := by
    have h := (HasFDerivAt.comp_hasDerivAt s V.form.hasFDerivAt (hq s)).clm_apply (hq s)
    convert h using 1
    · rfl
    · simp only [Function.comp_apply, map_neg, neg_apply,
        V.symmetric (q s) (relativeRiesz V E (q s)), relativeRiesz_spec]
      ring
  have hanti : Antitone (fun s => V.form (q s) (q s)) :=
    antitone_of_hasDerivAt_nonpos henergy (fun s => by
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (E.nonneg (q s)))
  simpa only [q, neg_zero, zero_smul, NormedSpace.exp_zero,
    one_apply_eq_self] using hanti ht

/-- Theorem 3.1, uniform half-line estimate: viscous norm equivalence
gives a semigroup bound independent of time. -/
theorem relativeSemigroup_norm_le (V E : CoerciveForm H) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (hV : V.HasBounds α β)
    (u : H) (t : ℝ) (ht : 0 ≤ t) :
    ‖(NormedSpace.exp (-t • relativeRiesz V E)) u‖ ≤ Real.sqrt (β / α) * ‖u‖ := by
  have he : α * ‖(NormedSpace.exp (-t • relativeRiesz V E)) u‖ ^ 2 ≤
      β * ‖u‖ ^ 2 :=
    (hV _).1.trans ((relativeSemigroup_energy_le V E u t ht).trans (hV u).2)
  have hsq : ‖(NormedSpace.exp (-t • relativeRiesz V E)) u‖ ^ 2 ≤
      (Real.sqrt (β / α) * ‖u‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hβ hα.le)]
    calc
      _ ≤ (β * ‖u‖ ^ 2) / α := (le_div_iff₀ hα).2 (by nlinarith [he])
      _ = _ := by ring
  nlinarith [norm_nonneg ((NormedSpace.exp (-t • relativeRiesz V E)) u),
    mul_nonneg (Real.sqrt_nonneg (β / α)) (norm_nonneg u)]

end KVApproximation.OperatorTheory
