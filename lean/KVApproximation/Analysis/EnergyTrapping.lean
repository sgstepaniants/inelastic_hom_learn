module

public import KVApproximation.Analysis.EnergyComparison
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Trapping by a conditional energy inequality
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Proposition B.13 (`eq:zeta_uniform_bound`), first-exit argument:
an energy estimate valid inside the closed error tube keeps the curve
strictly inside that tube and gives the exact finite-time error bound. -/
theorem ac_energy_trapping_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q v : ℝ → E} {a b rate forcing margin : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b) (hq₀ : q a = 0)
    (hRate : 0 < rate) (hforcing : 0 < forcing) (hMargin : 0 < margin)
    (hmargin : forcing ≤ rate * margin)
    (hderiv : ∀ᵐ s ∂volume.restrict (Icc a b), HasDerivAt q (v s) s)
    (henergy : ∀ᵐ s ∂volume.restrict (Icc a b), ‖q s‖ ≤ margin →
      ⟪q s, v s⟫_ℝ ≤ forcing * ‖q s‖ - rate * ‖q s‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖q t‖ ≤ forcing / rate * (1 - Real.exp (-rate * (t - a))) ∧ ‖q t‖ < margin := by
  have hab : a ≤ b := ht.1.trans ht.2
  have hn : ContinuousOn (fun s => ‖q s‖) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hq.continuousOn.norm
  have hstrict (t : ℝ) (ht : t ∈ Icc a b) : ‖q t‖ < margin := by
    by_contra! hbad
    have hnt : ContinuousOn (fun s => ‖q s‖) (Icc a t) :=
      hn.mono (Icc_subset_Icc_right ht.2)
    obtain ⟨u, hu, hueq⟩ := intermediate_value_Icc ht.1 hnt
      (show margin ∈ Icc ‖q a‖ ‖q t‖ from ⟨by simpa only [hq₀, norm_zero] using hMargin.le, hbad⟩)
    let S : Set ℝ := Icc a t ∩ (fun s => ‖q s‖) ⁻¹' {margin}
    have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hnt.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
    obtain ⟨τ, hτ⟩ := hS.exists_isLeast ⟨u, hu, hueq⟩
    have hτmem : τ ∈ Icc a t := hτ.1.1
    have hτeq : ‖q τ‖ = margin := hτ.1.2
    have hinside (s : ℝ) (hs : s ∈ Icc a τ) : ‖q s‖ ≤ margin := by
      by_contra! hbig
      have hns := hnt.mono (Icc_subset_Icc_right (hs.2.trans hτmem.2))
      obtain ⟨r, hr, hreq⟩ := intermediate_value_Ico hs.1 hns
        (show margin ∈ Ico ‖q a‖ ‖q s‖ from
          ⟨by simpa only [hq₀, norm_zero] using hMargin.le, hbig⟩)
      have hτr : τ ≤ r := hτ.2 ⟨⟨hr.1, hr.2.le.trans (hs.2.trans hτmem.2)⟩, hreq⟩
      exact (hr.2.trans_le hs.2).not_ge hτr
    have hqτ : AbsolutelyContinuousOnInterval q a τ := hq.mono (by
      rw [uIcc_of_le hτmem.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right (hτmem.2.trans ht.2))
    have hdτ := ae_restrict_of_ae_restrict_of_subset
      (Icc_subset_Icc_right (hτmem.2.trans ht.2)) hderiv
    have heτ : ∀ᵐ s ∂volume.restrict (Icc a τ),
        ⟪q s, v s⟫_ℝ ≤ forcing * ‖q s‖ - rate * ‖q s‖ ^ 2 := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (Icc_subset_Icc_right (hτmem.2.trans ht.2)) henergy,
        ae_restrict_mem measurableSet_Icc] with s hs hsmem
      exact hs (hinside s hsmem)
    have hbound := ac_energy_decay_bound hqτ hRate hforcing.le hdτ heτ
      (right_mem_Icc.mpr hτmem.1)
    simp only [hq₀, norm_zero, zero_mul, zero_add, hτeq] at hbound
    exact (finite_time_decay_lt_margin (t := τ - a) hRate hforcing hmargin).not_ge hbound
  refine ⟨?_, hstrict t ht⟩
  have he : ∀ᵐ s ∂volume.restrict (Icc a b),
      ⟪q s, v s⟫_ℝ ≤ forcing * ‖q s‖ - rate * ‖q s‖ ^ 2 := by
    filter_upwards [henergy, ae_restrict_mem measurableSet_Icc] with s hs hsmem
    exact hs (hstrict s hsmem).le
  simpa only [hq₀, norm_zero, zero_mul, zero_add] using
    ac_energy_decay_bound hq hRate hforcing.le hderiv he ht

end KVApproximation.Analysis
