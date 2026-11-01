module

public import KVApproximation.Analysis.PeriodicSmoothSobolev
public import KVApproximation.Analysis.PeriodicMeanRemoval
public import KVApproximation.Analysis.PeriodicKorn
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Nonzero strains from periodic displacements
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Proposition 4.7 (`prop:no_spectral_stability`), corrector construction:
subtracting the mean of a nonconstant periodic displacement preserves its
symmetric gradient and gives a nonzero strain in the zero-mean space. -/
theorem PeriodicC1.exists_zeroMean_nonzero_strain {d : ℕ}
    (φ : PeriodicC1 d (EuclideanSpace ℝ (Fin d)))
    (hnonconstant : ∃ y z, φ.value y ≠ φ.value z) :
    ∃ v : ZeroMeanPeriodicH1 d,
      (PeriodicH1.valueL d (v : PeriodicH1 d) =ᵐ[cellMeasure d]
        fun y => φ.value y - ∫ z, φ.value z ∂cellMeasure d) ∧
      (correctorGradientL d v =ᵐ[cellMeasure d]
        fun y => symmetrizeL d (periodicGradient φ.value y)) ∧
      correctorGradientL d v ≠ 0 := by
  obtain ⟨u, hu, hgu⟩ := φ.exists_periodicH1
  obtain ⟨v, hv, hgv⟩ := PeriodicH1.exists_zeroMean_same_gradient u
  let m := cellAverageL d (PeriodicH1.valueL d u)
  have hm : m = ∫ z, φ.value z ∂cellMeasure d :=
    (cellAverageL_eq_integral (PeriodicH1.valueL d u)).trans (integral_congr_ae hu)
  have hstrain : correctorGradientL d v =
      (symmetrizeL d).compLpL 2 (cellMeasure d) (PeriodicH1.gradientL d u) := by
    change (symmetrizeL d).compLpL 2 (cellMeasure d)
      (PeriodicH1.gradientL d (v : PeriodicH1 d)) = _
    rw [hgv]
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [hv]
    filter_upwards [hu,
      Lp.coeFn_sub (PeriodicH1.valueL d u) (Lp.const 2 (cellMeasure d) m),
      Lp.coeFn_const 2 (cellMeasure d) m] with y hy hsub hconst
    exact hsub.trans (by
      change PeriodicH1.valueL d u y - (Lp.const 2 (cellMeasure d) m) y = _
      rw [hy, hconst]
      exact congrArg (fun z => φ.value y - z) hm)
  · rw [hstrain]
    filter_upwards [(symmetrizeL d).coeFn_compLpL (PeriodicH1.gradientL d u), hgu]
      with y hs hg
    exact hs.trans (congrArg (symmetrizeL d) hg)
  · intro hz
    have hnorm := periodic_korn_two v
    have hgradnorm : ‖correctorGradientL d v‖ = 0 :=
      (Lp.norm_eq_zero_iff (by norm_num : 0 < (2 : ENNReal))).mpr hz
    rw [hgradnorm, mul_zero] at hnorm
    have hvzero : v = 0 :=
      (norm_eq_zero (E := ZeroMeanPeriodicH1 d) (a := v)).mp
        (le_antisymm hnorm (norm_nonneg v))
    have hvalue : PeriodicH1.valueL d u = Lp.const 2 (cellMeasure d) m := by
      have hv' := hv
      rw [hvzero] at hv'
      change PeriodicH1.valueL d 0 = PeriodicH1.valueL d u -
        Lp.const 2 (cellMeasure d) m at hv'
      rw [map_zero] at hv'
      exact sub_eq_zero.mp hv'.symm
    have hae : φ.value =ᵐ[cellMeasure d] fun _ => m := by
      apply hu.symm.trans
      rw [hvalue]
      exact Lp.coeFn_const 2 (cellMeasure d) m
    let : Measure.IsOpenPosMeasure (cellMeasure d) := by
      unfold cellMeasure
      infer_instance
    have heq : φ.value = fun _ => m :=
      Measure.eq_of_ae_eq hae φ.continuous_value continuous_const
    obtain ⟨y, z, hyz⟩ := hnonconstant
    exact hyz ((congrFun heq y).trans (congrFun heq z).symm)

end KVApproximation.Analysis
