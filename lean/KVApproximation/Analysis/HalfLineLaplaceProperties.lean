module

public import KVApproximation.Analysis.HalfLineLaplace
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrability and weak convergence of half-line Laplace transforms
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, Laplace-domain argument: bounded continuous trajectories
have genuine Bochner-integrable transforms at every positive real rate. -/
theorem integrable_halfLineLaplace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℝ → F) (hu : ContinuousOn u (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖u t‖ ≤ M) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t => Real.exp (-s * t) • u t) (Set.Ioi (0 : ℝ)) := by
  have hexp : Continuous (fun t : ℝ => Real.exp (-s * t)) := by fun_prop
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const M).mono'
    (((hexp.continuousOn.smul hu).mono Set.Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖Real.exp (-s * t) • u t‖ ≤ Real.exp (-s * t) * M
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hbound t ht.le) (Real.exp_pos _).le

/-- Theorem 3.1, Laplace convergence: a common half-line bound and
pointwise weak convergence imply weak convergence of the Bochner transforms.
The rate and functional are chosen after the convergent sequence. -/
theorem halfLineLaplace_weak_tendsto {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (u : ℕ → ℝ → F) (uLim : ℝ → F)
    (hu : ∀ n, ContinuousOn (u n) (Set.Ici (0 : ℝ)))
    (hLim : ContinuousOn uLim (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ n t, 0 ≤ t → ‖u n t‖ ≤ M)
    (hLimBound : ∀ t, 0 ≤ t → ‖uLim t‖ ≤ M)
    (hweak : ∀ t, 0 ≤ t → ∀ ℓ : F →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u n t)) atTop (𝓝 (ℓ (uLim t))))
    {s : ℝ} (hs : 0 < s) (ℓ : F →L[ℝ] ℝ) :
    Tendsto (fun n => ℓ (halfLineLaplace (u n) s)) atTop
      (𝓝 (ℓ (halfLineLaplace uLim s))) := by
  have hint (n : ℕ) := integrable_halfLineLaplace (u n) (hu n) (hbound n) hs
  have hLimInt := integrable_halfLineLaplace uLim hLim hLimBound hs
  have hcomm (n : ℕ) :
      (∫ t in Set.Ioi (0 : ℝ), ℓ (Real.exp (-s * t) • u n t)) =
        ℓ (halfLineLaplace (u n) s) := ℓ.integral_comp_comm (hint n)
  have hcommLim :
      (∫ t in Set.Ioi (0 : ℝ), ℓ (Real.exp (-s * t) • uLim t)) =
        ℓ (halfLineLaplace uLim s) := ℓ.integral_comp_comm hLimInt
  have hconv :
      Tendsto (fun n => ∫ t in Set.Ioi (0 : ℝ), ℓ (Real.exp (-s * t) • u n t)) atTop
        (𝓝 (∫ t in Set.Ioi (0 : ℝ), ℓ (Real.exp (-s * t) • uLim t))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun t => Real.exp (-s * t) * (‖ℓ‖ * M))
    · intro n
      exact (ℓ.integrable_comp (hint n)).aestronglyMeasurable
    · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const (‖ℓ‖ * M)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        ‖ℓ (Real.exp (-s * t) • u n t)‖ = Real.exp (-s * t) * ‖ℓ (u n t)‖ := by
          rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (-s * t) * (‖ℓ‖ * ‖u n t‖) :=
          mul_le_mul_of_nonneg_left (ℓ.le_opNorm _) (Real.exp_pos _).le
        _ ≤ Real.exp (-s * t) * (‖ℓ‖ * M) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hbound n t ht.le) (norm_nonneg ℓ))
            (Real.exp_pos _).le
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [map_smul, smul_eq_mul] using
        tendsto_const_nhds.mul (hweak t ht.le ℓ)
  simpa only [hcomm, hcommLim] using hconv

end KVApproximation.Analysis
