module

public import KVApproximation.Analysis.PeriodicAveraging

/-!
# Real and finite-dimensional periodic weak averaging

Real-part transport gives scalar averaging. A finite orthonormal basis
then gives weak averaging for the displacement and Frobenius tensor fields.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, static periodic homogenization: real periodic L² fields
converge weakly to their normalized cell means on bounded measurable domains. -/
theorem tendsto_integral_rescalePeriodic_mul_real {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) {f : PeriodicCell d → ℝ}
    (hf : MemLp f 2 (cellMeasure d)) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : MemLp g 2 (volume.restrict Ω)) :
    Tendsto (fun ε : ℝ => ∫ x in Ω, rescalePeriodic f ε x * g x)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ y, f y ∂cellMeasure d) * ∫ x in Ω, g x)) := by
  have h := tendsto_integral_rescalePeriodic_mul hΩ hΩm
    (hf.ofReal (K := ℂ)) (hg.ofReal (K := ℂ))
  change Tendsto (fun ε : ℝ =>
    ∫ x in Ω, ((rescalePeriodic f ε x : ℝ) : ℂ) * (g x : ℂ))
    (𝓝[>] (0 : ℝ))
    (𝓝 ((∫ y, (f y : ℂ) ∂cellMeasure d) * ∫ x in Ω, (g x : ℂ))) at h
  simp_rw [← Complex.ofReal_mul, integral_complex_ofReal] at h
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, ← Complex.ofReal_mul, Complex.ofReal_re] using hr

/-- Theorem 3.1, oscillating displacement and strain fields: periodic L²
fields in any finite-dimensional real Hilbert space converge weakly to
their cell means against every physical L² test field. -/
theorem tendsto_integral_rescalePeriodic_inner {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) {f : PeriodicCell d → F}
    (hf : MemLp f 2 (cellMeasure d)) {g : EuclideanSpace ℝ (Fin d) → F}
    (hg : MemLp g 2 (volume.restrict Ω)) :
    Tendsto (fun ε : ℝ => ∫ x in Ω, inner ℝ (rescalePeriodic f ε x) (g x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (∫ y, f y ∂cellMeasure d) (∫ x in Ω, g x))) := by
  classical
  let : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩ.measure_lt_top.ne
  let b := stdOrthonormalBasis ℝ F
  have hinner (x y : F) :
      (∑ i, inner ℝ (b i) x * inner ℝ (b i) y) = inner ℝ x y := by
    simpa only [real_inner_comm x] using b.sum_inner_mul_inner x y
  have hfi := hf.integrable (by norm_num)
  have hgi := hg.integrable (by norm_num)
  have hcoord (i : Fin (Module.finrank ℝ F)) :
      Tendsto (fun ε : ℝ =>
        ∫ x in Ω, inner ℝ (b i) (rescalePeriodic f ε x) * inner ℝ (b i) (g x))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (b i) (∫ y, f y ∂cellMeasure d) *
          inner ℝ (b i) (∫ x in Ω, g x))) := by
    simpa only [rescalePeriodic, integral_inner hfi, integral_inner hgi] using
      tendsto_integral_rescalePeriodic_mul_real hΩ hΩm
        (hf.const_inner (b i)) (hg.const_inner (b i))
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  rw [hinner] at hsum
  apply hsum.congr'
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with ε hε hε₁
    exact ⟨hε, hε₁.le⟩
  filter_upwards [hsmall] with ε hε
  have hres := memLp_two_rescalePeriodic hΩ hε.1 hε.2 hf
  symm
  calc
    (∫ x in Ω, inner ℝ (rescalePeriodic f ε x) (g x)) =
        ∫ x in Ω, ∑ i, inner ℝ (b i) (rescalePeriodic f ε x) * inner ℝ (b i) (g x) := by
      congr 1
      funext x
      exact (hinner _ _).symm
    _ = ∑ i, ∫ x in Ω,
        inner ℝ (b i) (rescalePeriodic f ε x) * inner ℝ (b i) (g x) :=
      integral_finsetSum _ fun i _ =>
        (hres.const_inner (b i)).integrable_mul (hg.const_inner (b i))

end KVApproximation.Analysis
