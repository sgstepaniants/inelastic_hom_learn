module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Regularity of integral curves with bounded velocity
-/

public section

open MeasureTheory Set
open scoped NNReal Topology

namespace KVApproximation.Dynamics

/-- Proposition B.13, integral-to-differential bridge: an integral curve
with an essentially bounded integrable velocity is absolutely continuous
and has that velocity as its derivative almost everywhere. -/
theorem integral_curve_regularity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {q v : ℝ → E} {a b : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hv : IntervalIntegrable v volume a b)
    (hK : ∀ᵐ s ∂volume.restrict (Icc a b), ‖v s‖ ≤ K)
    (hq : ∀ t ∈ Icc a b, q t = q a + ∫ s in a..t, v s) :
    AbsolutelyContinuousOnInterval q a b ∧
      ∀ᵐ s ∂volume.restrict (Icc a b), HasDerivAt q (v s) s := by
  have hInt (t : ℝ) (ht : t ∈ Icc a b) : IntervalIntegrable v volume a t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hv |>.mono_set
        (Icc_subset_Icc_right ht.2))
  have hLip : LipschitzOnWith K q (Icc a b) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro s hs t ht
    rw [dist_eq_norm, hq s hs, hq t ht, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hInt s hs) (hInt t ht)]
    simp only [Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hK] with r hr hrst
    apply hr
    exact ⟨(le_min ht.1 hs.1).trans hrst.1.le,
      hrst.2.trans (max_le ht.2 hs.2)⟩
  refine ⟨(show LipschitzOnWith K q (uIcc a b) by
    simpa only [uIcc_of_le hab] using hLip).absolutelyContinuousOnInterval, ?_⟩
  have hEndpoints : ∀ᵐ s ∂volume.restrict (Icc a b), s ∈ Ioo a b := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [ae_restrict_of_ae hv.ae_hasDerivAt_integral, hEndpoints] with s hs hsmem
  have hsI : s ∈ uIcc a b := by simpa only [uIcc_of_le hab] using Ioo_subset_Icc_self hsmem
  have haI : a ∈ uIcc a b := left_mem_uIcc
  apply ((hs hsI a haI).const_add (q a)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hsmem.1 hsmem.2] with t ht
  exact hq t ht

end KVApproximation.Dynamics
