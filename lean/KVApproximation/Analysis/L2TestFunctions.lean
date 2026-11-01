module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Smooth tests separate L² fields

Pairing a localized vector integral with every constant vector determines
the integral. The vector-valued fundamental lemma then identifies the
field without choosing coordinates or intersecting uncountably many
sets of full measure.
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions InnerProductSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, identification of weak stress limits: smooth localized
constant-vector pairings determine an L² field on any open domain. -/
theorem eq_of_integral_testFunction_inner_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {Ω : Opens E}
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (p q : Lp F 2 (μ.restrict (Ω : Set E)))
    (h : ∀ (χ : 𝓓(Ω, ℝ)) (e : F),
      (∫ x in (Ω : Set E), χ x * ⟪p x, e⟫_ℝ ∂μ) =
        ∫ x in (Ω : Set E), χ x * ⟪q x, e⟫_ℝ ∂μ) : p = q := by
  have hmem : MemLp (fun x => p x - q x) 2 (μ.restrict (Ω : Set E)) :=
    (Lp.memLp p).sub (Lp.memLp q)
  have hz : ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → p x - q x = 0 := by
    apply Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hmem.locallyIntegrable (by norm_num)))
    intro φ hφ hφc hφs
    let χ : 𝓓(Ω, ℝ) := ⟨φ, hφ, hφc, hφs⟩
    have hχ : MemLp (φ : E → ℝ) 2 (μ.restrict (Ω : Set E)) :=
      χ.continuous.memLp_of_hasCompactSupport χ.hasCompactSupport
    have hp : Integrable (fun x => φ x • p x) (μ.restrict (Ω : Set E)) :=
      memLp_one_iff_integrable.mp (hχ.smul (Lp.memLp p))
    have hq : Integrable (fun x => φ x • q x) (μ.restrict (Ω : Set E)) :=
      memLp_one_iff_integrable.mp (hχ.smul (Lp.memLp q))
    have hvec : (∫ x in (Ω : Set E), φ x • p x ∂μ) =
        ∫ x in (Ω : Set E), φ x • q x ∂μ := by
      apply ext_inner_left ℝ
      intro e
      rw [← integral_inner hp, ← integral_inner hq]
      have htest := h χ e
      change (∫ x in (Ω : Set E), φ x * ⟪p x, e⟫_ℝ ∂μ) =
        ∫ x in (Ω : Set E), φ x * ⟪q x, e⟫_ℝ ∂μ at htest
      simpa only [real_inner_smul_right, real_inner_comm] using htest
    calc
      (∫ x, φ x • (p x - q x) ∂μ) =
          ∫ x in (Ω : Set E), φ x • (p x - q x) ∂μ := by
        rw [← integral_indicator Ω.isOpen.measurableSet]
        congr 1
        symm
        apply Set.indicator_eq_self.2
        exact (Function.support_smul_subset_left φ (fun x => p x - q x)).trans
          ((subset_tsupport φ).trans hφs)
      _ = 0 := by
        simp_rw [smul_sub]
        rw [integral_sub hp hq, hvec, sub_self]
  apply Lp.ext
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  exact hz.mono fun x hx hxΩ => sub_eq_zero.mp (hx hxΩ)

end KVApproximation.Analysis
