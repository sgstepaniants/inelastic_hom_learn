module

public import KVApproximation.Analysis.TimeSobolevNorms
public import KVApproximation.Dynamics.LinearTimeDuhamel

/-!
# Finite-time bounds for bounded linear evolution

Duhamel's formula and Cauchy–Schwarz turn a semigroup bound into a
uniform trace bound. The evolution equation then controls the full H¹ norm.
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.Dynamics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, forced evolution estimate: a semigroup bound and Cauchy–Schwarz
control the continuous trace on the entire closed interval. -/
theorem linear_timeH1_trace_norm_le (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {M : ℝ} (hM : 0 ≤ M)
    (hsemigroup : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : H,
      ‖(NormedSpace.exp (s • A)) x‖ ≤ M * ‖x‖)
    (f : Lp H 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t)
    (t : Set.Icc (0 : ℝ) T) :
    ‖TimeH1.trace hT u t‖ ≤ M * (‖TimeH1.initial hT u‖ + Real.sqrt T * ‖f‖) := by
  have hfint : IntervalIntegrable (fun s => ‖f s‖) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2
      ((Lp.memLp f).integrable (by norm_num)).norm
  have hfshort : IntervalIntegrable (fun s => M * ‖f s‖) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le t.property.1).2
      (IntegrableOn.mono_set (((Lp.memLp f).integrable (by norm_num)).norm.const_mul M)
        (Set.Ioo_subset_Ioo le_rfl t.property.2))
  have hL1 : (∫ s in (0 : ℝ)..T, ‖f s‖) ≤ Real.sqrt T * ‖f‖ := by
    rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo]
    convert Lp.integral_norm_le_mul_norm f using 1
    simp only [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofNat]
    norm_num only [show (1 - 1 / (2 : ℝ)) = 1 / 2 by norm_num]
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hT.le, Real.sqrt_eq_rpow]
  have hconvolution :
      ‖∫ s in (0 : ℝ)..(t : ℝ), (NormedSpace.exp (((t : ℝ) - s) • A)) (f s)‖ ≤
        M * (Real.sqrt T * ‖f‖) := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..(t : ℝ), M * ‖f s‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le t.property.1 _ hfshort
        exact Filter.Eventually.of_forall fun s hs =>
          hsemigroup ((t : ℝ) - s) ⟨sub_nonneg.2 hs.2, by linarith [t.property.2, hs.1]⟩ (f s)
      _ = M * ∫ s in (0 : ℝ)..(t : ℝ), ‖f s‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ M * ∫ s in (0 : ℝ)..T, ‖f s‖ := by
        apply mul_le_mul_of_nonneg_left _ hM
        exact intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
          (Filter.Eventually.of_forall fun s => norm_nonneg (f s)) hfint
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 hM
  rw [linear_timeH1_duhamel A hT f (Lp.memLp f) u hode t]
  calc
    _ ≤ ‖(NormedSpace.exp ((t : ℝ) • A)) (TimeH1.initial hT u)‖ +
        ‖∫ s in (0 : ℝ)..(t : ℝ), (NormedSpace.exp (((t : ℝ) - s) • A)) (f s)‖ := norm_add_le _ _
    _ ≤ M * ‖TimeH1.initial hT u‖ + M * (Real.sqrt T * ‖f‖) :=
      add_le_add (hsemigroup t t.property _) hconvolution
    _ = _ := by ring

/-- Theorem 3.1, forced evolution estimate: the same semigroup bound
controls the actual full finite-time H¹ norm. -/
theorem linear_timeH1_norm_le (A : H →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    {M : ℝ} (hM : 0 ≤ M)
    (hsemigroup : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : H,
      ‖(NormedSpace.exp (s • A)) x‖ ≤ M * ‖x‖)
    (f : Lp H 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t) :
    ‖u‖ ≤ (1 + ‖A‖) * Real.sqrt T *
      (M * (‖TimeH1.initial hT u‖ + Real.sqrt T * ‖f‖)) + ‖f‖ := by
  have hvalue : ‖TimeH1.valueL2 u‖ ≤ Real.sqrt T *
      (M * (‖TimeH1.initial hT u‖ + Real.sqrt T * ‖f‖)) := by
    have h := Lp.norm_le_of_ae_bound (f := TimeH1.valueL2 u)
      (mul_nonneg hM (add_nonneg (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg T) (norm_nonneg f))))
      (by
        filter_upwards [TimeH1.trace_ae hT u] with t ht
        rw [TimeH1.valueL2_apply, ht]
        exact linear_timeH1_trace_norm_le A hT hM hsemigroup f u hode
          (Set.projIcc 0 T hT.le t))
    convert h using 1
    simp only [measureUnivNNReal, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofNat]
    change Real.sqrt T * _ = (ENNReal.ofReal T).toReal ^ (2 : ℝ)⁻¹ * _
    rw [ENNReal.toReal_ofReal hT.le, Real.sqrt_eq_rpow]
    simp only [one_div]
  calc
    _ ≤ (1 + ‖A‖) * ‖TimeH1.valueL2 u‖ + ‖f‖ := TimeH1.norm_le_of_ode A f u hode
    _ ≤ (1 + ‖A‖) * (Real.sqrt T *
        (M * (‖TimeH1.initial hT u‖ + Real.sqrt T * ‖f‖))) + ‖f‖ := by
      gcongr
    _ = _ := by ring

end KVApproximation.Dynamics
