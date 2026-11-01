module

public import KVApproximation.Analysis.PeriodicSobolevIdentities

/-!
# Removing the mean from periodic displacement tests
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Section 3.1 and Appendix A.3: every constant displacement is a
periodic H¹ field with zero gradient. -/
theorem PeriodicH1.exists_constant {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) :
    ∃ u : PeriodicH1 d,
      PeriodicH1.valueL d u = Lp.const 2 (cellMeasure d) c ∧
      PeriodicH1.gradientL d u = 0 := by
  let j : PeriodicJetField d := Lp.const 2 (cellMeasure d) (WithLp.toLp 2 (c, (0 : SecondOrder d)))
  have hgrad (y : PeriodicCell d) : periodicGradient (fun _ => c) y = 0 := by
    ext ij
    simp [periodicGradient]
  have hj : j ∈ periodicH1Submodule d := by
    apply (Submodule.span ℝ (smoothPeriodicJets d)).le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨fun _ => c, contDiff_const, ?_⟩
    filter_upwards [Lp.coeFn_const 2 (cellMeasure d) (WithLp.toLp 2 (c, (0 : SecondOrder d)))]
      with y hy
    exact hy.trans (by rw [hgrad]; rfl)
  let u : PeriodicH1 d := ⟨j, hj⟩
  refine ⟨u, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards
      [(WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL j,
        Lp.coeFn_const 2 (cellMeasure d) (WithLp.toLp 2 (c, (0 : SecondOrder d))),
        Lp.coeFn_const 2 (cellMeasure d) c] with y hp hjy hcy
    change ((WithLp.fstL 2 ℝ _ _).compLpL 2 (cellMeasure d) j) y = _
    rw [hp, hjy, hcy]
    rfl
  · apply Lp.ext
    filter_upwards
      [(WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL j,
        Lp.coeFn_const 2 (cellMeasure d) (WithLp.toLp 2 (c, (0 : SecondOrder d))),
        (Lp.coeFn_zero (E := SecondOrder d) (p := 2) (μ := cellMeasure d))]
      with y hp hjy hzero
    change ((WithLp.sndL 2 ℝ _ _).compLpL 2 (cellMeasure d) j) y = _
    rw [hp, hjy, hzero]
    rfl

/-- Appendix A.3, testing the balance equation in `eq:cell_weak`:
subtracting the mean leaves the full periodic weak gradient unchanged. -/
theorem PeriodicH1.exists_zeroMean_same_gradient {d : ℕ} (u : PeriodicH1 d) :
    ∃ v : ZeroMeanPeriodicH1 d,
      PeriodicH1.valueL d (v : PeriodicH1 d) = PeriodicH1.valueL d u -
        Lp.const 2 (cellMeasure d) (cellAverageL d (PeriodicH1.valueL d u)) ∧
      PeriodicH1.gradientL d (v : PeriodicH1 d) = PeriodicH1.gradientL d u := by
  let m := cellAverageL d (PeriodicH1.valueL d u)
  obtain ⟨c, hc, hgc⟩ := PeriodicH1.exists_constant m
  have havg : cellAverageL d (PeriodicH1.valueL d c) = m := by
    rw [hc, cellAverageL_eq_integral]
    calc
      (∫ y, (Lp.const 2 (cellMeasure d) m) y ∂cellMeasure d) =
          ∫ _y, m ∂cellMeasure d := integral_congr_ae (Lp.coeFn_const 2 (cellMeasure d) m)
      _ = m := by simp
  have hmem : u - c ∈ zeroMeanPeriodicSubmodule d := by
    change cellAverageL d (PeriodicH1.valueL d (u - c)) = 0
    rw [map_sub, map_sub, havg]
    exact sub_self m
  refine ⟨⟨u - c, hmem⟩, ?_, ?_⟩
  · change PeriodicH1.valueL d (u - c) = _
    rw [map_sub, hc]
  · change PeriodicH1.gradientL d (u - c) = _
    rw [map_sub, hgc, sub_zero]

end KVApproximation.Analysis
