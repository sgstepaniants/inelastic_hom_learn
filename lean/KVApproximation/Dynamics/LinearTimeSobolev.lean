module

public import KVApproximation.Analysis.TimeSobolevProperties
public import KVApproximation.Dynamics.Caratheodory

/-!
# Linear evolution with square-integrable forcing
-/

public section

open MeasureTheory Set
open KVApproximation.Analysis

namespace KVApproximation.Dynamics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Appendix A.3: a continuous curve on a finite interval lies in L². -/
private theorem continuousOn_memLp_Ioo {T : ℝ} {q : ℝ → H}
    (hq : ContinuousOn q (Icc 0 T)) :
    MemLp q 2 (volume.restrict (Ioo 0 T)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have hb : MemLp q ⊤ (volume.restrict (Icc 0 T)) := by
    apply memLp_top_of_bound (hq.aestronglyMeasurable measurableSet_Icc) C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hC t ht
  rw [restrict_Ioo_eq_restrict_Icc]
  exact hb.mono_exponent le_top

omit [CompleteSpace H] in
/-- Appendix A.3: the affine field is integrable along continuous state curves. -/
private theorem linear_integrableOn (A : H →L[ℝ] H) {T : ℝ} {f : ℝ → H}
    (hf : MemLp f 2 (volume.restrict (Ioo 0 T))) {q : ℝ → H}
    (hq : ContinuousOn q (Icc 0 T)) :
    IntegrableOn (fun t => A (q t) + f t) (Icc 0 T) := by
  rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  exact (((continuousOn_memLp_Ioo hq).continuousLinearMap_comp A).add hf).integrable
    (by norm_num)

/-- Appendix A.3: the canonical trace represents the same integral solution. -/
private theorem timeH1_trace_eqOn {T : ℝ} (hT : 0 < T) (u : TimeH1 H T)
    {q : ℝ → H} (hq : ContinuousOn q (Icc 0 T))
    (hu : TimeH1.value u =ᵐ[volume.restrict (Ioo 0 T)] q) :
    EqOn (fun t => TimeH1.trace hT u (projIcc 0 T hT.le t)) q (Icc 0 T) := by
  have h := (TimeH1.trace_ae hT u).symm.trans hu
  rw [restrict_Ioo_eq_restrict_Icc] at h
  exact Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hT) h
    ((TimeH1.trace hT u).continuous.comp continuous_projIcc).continuousOn hq

/-- Appendix A.3: integrating the weak equation gives its continuous integral form. -/
private theorem linear_timeH1_integral (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {f : ℝ → H} (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    TimeH1.trace hT u (projIcc 0 T hT.le t) = TimeH1.initial hT u +
      ∫ s in (0 : ℝ)..t, A (TimeH1.trace hT u (projIcc 0 T hT.le s)) + f s := by
  have hae : TimeH1.velocity u =ᵐ[volume.restrict (Icc 0 T)]
      fun s => A (TimeH1.trace hT u (projIcc 0 T hT.le s)) + f s := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hode, TimeH1.trace_ae hT u] with s hs htr
    rw [hs, htr]
  have hi : (∫ s in (0 : ℝ)..t, TimeH1.velocity u s) =
      ∫ s in (0 : ℝ)..t, A (TimeH1.trace hT u (projIcc 0 T hT.le s)) + f s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_imp_of_ae_restrict hae] with s hs hst
    rw [uIoc_of_le ht.1] at hst
    exact hs ⟨hst.1.le, hst.2.trans ht.2⟩
  rw [projIcc_of_mem hT.le ht, TimeH1.trace_integral, hi]

/-- Appendix A.3 (`eq:cell_ode`): a bounded linear evolution equation with
square-integrable forcing has a unique finite-time H¹ solution. -/
theorem linear_timeH1_exists_unique (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    (f : ℝ → H) (hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T))) (q₀ : H) :
    ∃! u : TimeH1 H T,
      TimeH1.initial hT u = q₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity u t = A (TimeH1.value u t) + f t := by
  have hLip : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      LipschitzWith ‖A‖₊ (fun x => A x + f t) :=
    Filter.Eventually.of_forall fun t => LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [dist_add_right] using A.lipschitzWith.dist_le_mul x y
  have hInt : ∀ q : ℝ → H, ContinuousOn q (Icc 0 T) →
      IntegrableOn (fun t => A (q t) + f t) (Icc 0 T) :=
    fun _ hq => linear_integrableOn A hf hq
  obtain ⟨q, hq, hq₀, hqeq⟩ := exists_integral_solution_Icc hLip hInt q₀
  have hqLp := continuousOn_memLp_Ioo hq
  have hvLp : MemLp (fun t => A (q t) + f t) 2 (volume.restrict (Ioo 0 T)) :=
    (hqLp.continuousLinearMap_comp A).add hf
  have hweak : TauCeti.HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
      q (fun t => A (q t) + f t) 1 := by
    have hw := (TauCeti.hasWeakLineDerivOn_const q₀).add
      (TauCeti.hasWeakLineDerivOn_intervalIntegral_left
        (hvLp.integrable (by norm_num)))
    have hw' : TauCeti.HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
        (fun t => q₀ + ∫ s in (0 : ℝ)..t, A (q s) + f s)
        (fun t => A (q t) + f t) 1 := by
      simpa only [Pi.add_def, zero_add] using hw
    apply hw'.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hqeq t (Ioo_subset_Icc_self ht)).symm
  obtain ⟨u, huq, huv⟩ := TimeH1.exists_of_weak_derivative hqLp hvLp hweak
  have htrace := timeH1_trace_eqOn hT u hq huq
  have hu₀ : TimeH1.initial hT u = q₀ := by
    have h := htrace (x := 0) ⟨le_rfl, hT.le⟩
    simpa only [projIcc_of_mem hT.le (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩),
      TimeH1.initial, hq₀] using h
  have hode : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t := by
    filter_upwards [huv, huq] with t hv hq'
    rw [hv, hq']
  refine ⟨u, ⟨hu₀, hode⟩, ?_⟩
  intro w hw
  have heq := integral_solution_unique_Icc (x₀ := q₀) hLip hInt
    ((TimeH1.trace hT w).continuous.comp continuous_projIcc).continuousOn
    ((TimeH1.trace hT u).continuous.comp continuous_projIcc).continuousOn
    (fun t ht => by
      simpa only [Function.comp_apply, hw.1] using linear_timeH1_integral A hT w hw.2 ht)
    (fun t ht => by
      simpa only [Function.comp_apply, hu₀] using linear_timeH1_integral A hT u hode ht)
  apply TauCeti.EvolutionSpace.ext
  apply Lp.ext
  change TimeH1.value w =ᵐ[volume.restrict (Ioo 0 T)] TimeH1.value u
  filter_upwards [TimeH1.trace_ae hT w, TimeH1.trace_ae hT u,
    ae_restrict_mem measurableSet_Ioo] with t hwt hut ht
  exact hwt.trans ((heq (Ioo_subset_Icc_self ht)).trans hut.symm)

end KVApproximation.Dynamics
