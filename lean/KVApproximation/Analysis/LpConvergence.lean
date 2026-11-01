module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Dominated convergence in finite Lp spaces
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Dominated-convergence step used in Lemma B.1: an Lp majorant and a.e. convergence to zero
give convergence of the Lp norm, for every finite positive exponent. -/
theorem tendsto_eLpNorm_of_dominated_zero {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {p : ENNReal} (hp₀ : p ≠ 0) (hp_top : p ≠ ⊤)
    {F : ℕ → X → E} {bound : X → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hb : MemLp bound p μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p μ) atTop (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp_top
  have hpowlim : ∀ᵐ x ∂μ,
      Tendsto (fun n => ‖F n x‖ₑ ^ p.toReal) atTop (𝓝 (0 : ENNReal)) := by
    filter_upwards [hlim] with x hx
    simpa only [enorm_zero, ENNReal.zero_rpow_of_pos hp] using
      hx.enorm.ennrpow_const p.toReal
  have hdom := tendsto_lintegral_of_dominated_convergence'
    (fun x => ‖bound x‖ₑ ^ p.toReal)
    (fun n => (hF n).enorm.pow_const p.toReal)
    (fun n => (hbound n).mono fun x hx =>
      ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.mpr hx) hp.le)
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hp_top hb.eLpNorm_lt_top).ne
    hpowlim
  have hroot := hdom.ennrpow_const (1 / p.toReal)
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top (hF _),
    lintegral_zero, ENNReal.zero_rpow_of_pos (div_pos zero_lt_one hp)] using hroot

end KVApproximation.Analysis
