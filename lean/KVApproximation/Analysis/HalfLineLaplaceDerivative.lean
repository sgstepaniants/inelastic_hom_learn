module

public import KVApproximation.Analysis.HalfLineLaplaceProperties
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The Laplace transform of a classical derivative
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, Laplace-domain argument: integration by parts for a
bounded classical trajectory and its bounded continuous velocity.
Only positive-time derivatives and the trace at zero enter the formula. -/
theorem halfLineLaplace_derivative {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (f f' : ℝ → F)
    (hf : ContinuousOn f (Set.Ici (0 : ℝ)))
    (hf' : ContinuousOn f' (Set.Ici (0 : ℝ)))
    (hder : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    {M N : ℝ} (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖f t‖ ≤ M)
    (hbound' : ∀ t ∈ Set.Ici (0 : ℝ), ‖f' t‖ ≤ N)
    {s : ℝ} (hs : 0 < s) :
    halfLineLaplace f' s = s • halfLineLaplace f s - f 0 := by
  have hint := integrable_halfLineLaplace f hf hbound hs
  have hint' := integrable_halfLineLaplace f' hf' hbound' hs
  have hexp (t : ℝ) : HasDerivAt (fun r : ℝ => Real.exp (-s * r))
      (Real.exp (-s * t) * (-s)) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (-s)).exp
  have hweightedDeriv (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      HasDerivAt (fun r => Real.exp (-s * r) • f r)
        (Real.exp (-s * t) • f' t - s • (Real.exp (-s * t) • f t)) t := by
    simpa only [Pi.smul_def, mul_neg, neg_smul, mul_smul, sub_eq_add_neg,
      smul_comm s (Real.exp (-s * t))] using (hexp t).fun_smul (hder t ht)
  have hweightedCont : ContinuousOn (fun t => Real.exp (-s * t) • f t)
      (Set.Ici (0 : ℝ)) :=
    (show Continuous (fun t : ℝ => Real.exp (-s * t)) by fun_prop).continuousOn.smul hf
  have hexpLimit : Tendsto (fun t : ℝ => Real.exp (-s * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hs))
  have hweightedLimit : Tendsto (fun t => Real.exp (-s * t) • f t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t => Real.exp (-s * t) * M)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos _).le
    · simpa only [zero_mul] using hexpLimit.mul_const M
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (hweightedCont 0 le_rfl)
    hweightedDeriv (hint'.sub (hint.fun_smul s)) hweightedLimit
  have hidentity : halfLineLaplace f' s - s • halfLineLaplace f s = -f 0 := by
    simpa only [integral_sub hint' (hint.fun_smul s), integral_smul,
      halfLineLaplace, mul_zero, Real.exp_zero, one_smul, zero_sub] using hFTC
  calc
    halfLineLaplace f' s = -f 0 + s • halfLineLaplace f s :=
      sub_eq_iff_eq_add.mp hidentity
    _ = s • halfLineLaplace f s - f 0 := by rw [sub_eq_add_neg, add_comm]

end KVApproximation.Analysis
