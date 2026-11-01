module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.NormNum

/-!
# The L¹–L∞ interpolation step

Integrating the pointwise inequality `‖f‖² ≤ κ ‖f‖` gives the exact estimate
used to upgrade the BV subsequence in Lemma B.2 to L² convergence.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Lemma B.2 (`lem:bv_compact`), Hölder step: an essential pointwise bound
controls the squared L² norm by the L¹ norm, with constant one. -/
theorem eLpNorm_two_sq_le_of_ae_bound {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} {f : X → F} {κ : ℝ}
    (hf : AEStronglyMeasurable f μ) (hκ : 0 ≤ κ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ κ) :
    (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal κ * eLpNorm f 1 μ := by
  have hsq : (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
      eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf
  rw [hsq, eLpNorm_one_eq_lintegral_enorm hf,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hbound] with x hx
  rw [pow_two]
  apply mul_le_mul_left
  simpa only [ofReal_norm] using (ENNReal.ofReal_le_ofReal_iff hκ).2 hx

/-- Lemma B.2 (`lem:bv_compact`): L¹ convergence and a common essential bound
give L² convergence. The argument requires no finite-measure hypothesis. -/
theorem tendsto_eLpNorm_two_of_one_of_ae_bound {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} {f : ℕ → X → F} {κ : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hκ : 0 ≤ κ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ κ)
    (hconv : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => ENNReal.ofReal κ * eLpNorm (f n) 1 μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hconv (Or.inr ENNReal.ofReal_ne_top)
  have hsq : Tendsto (fun n => (eLpNorm (f n) 2 μ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.squeeze hupper (fun _ => zero_le)
      (fun n => eLpNorm_two_sq_le_of_ae_bound (hf n) hκ (hbound n))
  have hroot := hsq.ennrpow_const (1 / 2 : ℝ)
  simpa only [← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hroot

end KVApproximation.Analysis
