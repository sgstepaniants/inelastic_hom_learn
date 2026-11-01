module

public import KVApproximation.Analysis.PeriodicSmoothIdentities
public import KVApproximation.Analysis.PeriodicFourierSynthesis
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Tactic.Linarith

/-!
# Density of smooth periodic fields

A continuous L¹ approximation is bounded on the cell and hence lies in L².
Finite real Fourier sums approximate it in L² and therefore in L¹. An
orthonormal basis transports this construction to any finite-dimensional target.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Lemma B.2, periodic BV embedding: C¹ periodic fields are dense in L¹.
This is the approximation step used in the smooth-test norm formula. -/
theorem exists_periodicC1_eLpNorm_sub_lt (A : Lp F 1 (cellMeasure d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : PeriodicC1 d F,
      eLpNorm (fun y => A y - φ.value y) 1 (cellMeasure d) < ENNReal.ofReal ε := by
  classical
  let : (cellMeasure d).IsAddHaarMeasure := by unfold cellMeasure; infer_instance
  have hε₃ : 0 < ε / 3 := by linarith
  obtain ⟨g, hg, _⟩ := (Lp.memLp A).exists_boundedContinuous_eLpNorm_sub_le
    (by simp) (ENNReal.ofReal_pos.mpr hε₃).ne'
  let b := stdOrthonormalBasis ℝ F
  let G : C(PeriodicCell d, EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) :=
    ⟨fun y => b.repr (g y), b.repr.continuous.comp g.continuous⟩
  let U : Lp (EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) 2 (cellMeasure d) :=
    G.toLp 2 (cellMeasure d) ℝ
  let a (n : Fin d → ℤ) (i : Fin (Module.finrank ℝ F)) :=
    ∫ y, UnitAddTorus.mFourier (-n) y * (U y i : ℂ) ∂cellMeasure d
  have hsum := hasSum_realFourier_series U
  obtain ⟨s, hs⟩ := (hsum.eventually (Metric.ball_mem_nhds U hε₃)).exists
  let P : C(PeriodicCell d, EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) :=
    ∑ n ∈ s, realFourierMode n (a n)
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => P (toCell x)) := by
    simpa only [P, ContinuousMap.sum_apply] using
      ContDiff.sum (fun n (_ : n ∈ s) => contDiff_realFourierMode_lift n (a n))
  let φ : PeriodicC1 d F :=
    ⟨fun y => b.repr.symm (P y), (b.repr.symm.contDiff.comp hP).of_le (by simp)⟩
  have hPsum : P.toLp 2 (cellMeasure d) ℝ =
      ∑ n ∈ s, (realFourierMode n (a n)).toLp 2 (cellMeasure d) ℝ := by
    exact map_sum (ContinuousMap.toLp 2 (cellMeasure d) ℝ) _ _
  have hdist : dist (P.toLp 2 (cellMeasure d) ℝ) U < ε / 3 := by
    rw [hPsum]
    exact hs
  have hPG : eLpNorm (fun y => P y - G y) 2 (cellMeasure d) < ENNReal.ofReal (ε / 3) := by
    have heq : eLpNorm (fun y => P y - G y) 2 (cellMeasure d) =
        edist (P.toLp 2 (cellMeasure d) ℝ) U := by
      rw [Lp.edist_def]
      exact (eLpNorm_congr_ae ((P.coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d)).sub
        (G.coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d)))).symm
    rw [heq, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hε₃).2 hdist
  have hnorm : eLpNorm (fun y => φ.value y - g y) 2 (cellMeasure d) =
      eLpNorm (fun y => P y - G y) 2 (cellMeasure d) := by
    apply eLpNorm_congr_norm_ae
      ((φ.continuous_value.sub g.continuous).aestronglyMeasurable)
      ((P.continuous.sub G.continuous).aestronglyMeasurable)
    apply Eventually.of_forall
    intro y
    change ‖b.repr.symm (P y) - g y‖ = ‖P y - b.repr (g y)‖
    rw [← b.repr.norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply]
  have happrox : eLpNorm (fun y => g y - φ.value y) 1 (cellMeasure d) ≤
      ENNReal.ofReal (ε / 3) := by
    change eLpNorm (⇑g - φ.value) 1 (cellMeasure d) ≤ ENNReal.ofReal (ε / 3)
    rw [eLpNorm_sub_comm]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
      (hnorm.trans_lt hPG).le
  refine ⟨φ, ?_⟩
  have heq : (fun y => A y - φ.value y) = (⇑A - ⇑g) + (fun y => g y - φ.value y) := by
    ext y
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  calc
    eLpNorm (fun y => A y - φ.value y) 1 (cellMeasure d) ≤
        eLpNorm (⇑A - ⇑g) 1 (cellMeasure d) +
          eLpNorm (fun y => g y - φ.value y) 1 (cellMeasure d) := by
      rw [heq]
      exact eLpNorm_add_le le_rfl
    _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := add_le_add hg happrox
    _ < ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hε₃.le hε₃.le]
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

end KVApproximation.Analysis
