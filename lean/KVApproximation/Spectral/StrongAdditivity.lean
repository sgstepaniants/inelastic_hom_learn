module

public import ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Strong countable additivity of spectral projections

Appendix A.2 uses the spectral measure on an arbitrary Hilbert space. Finite
partial sums converge on each vector because the squared norm of their tail
equals the remaining mass of its scalar diagonal measure.
-/

public section

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace KVApproximation.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Appendix A.2: finite scalar additivity determines finite projection sums. -/
private theorem proj_finset_union (P : TauCeti.ProjValMeasure H)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (s : Finset ℕ) :
    P.proj (⋃ n ∈ s, B n) (MeasurableSet.biUnion (Finset.countable_toSet s) (fun n _ => hB n)) =
      ∑ n ∈ s, P.proj (B n) (hB n) := by
  apply TauCeti.op_ext_of_inner_self
  intro u
  simp only [sum_apply, inner_sum, P.inner_proj]
  rw [measure_biUnion_finset (fun i _ j _ hij => hd hij) (fun n _ => hB n),
    ENNReal.toReal_sum (fun n _ => measure_ne_top _ _)]
  simp

/-- Appendix A.2: the norm of a nested projection difference is its diagonal mass. -/
private theorem norm_sq_proj_sub (P : TauCeti.ProjValMeasure H)
    {B C : Set ℝ} (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : B ⊆ C)
    (u : H) :
    ‖P.proj B hB u - P.proj C hC u‖ ^ 2 =
      ((P.diag u) C).toReal - ((P.diag u) B).toReal := by
  have hinner : ⟪P.proj B hB u, P.proj C hC u⟫_ℂ =
      (((P.diag u) B).toReal : ℂ) := by
    rw [← ContinuousLinearMap.adjoint_inner_right,
      (P.isSelfAdjoint_proj B hB).adjoint_eq, ← mul_apply_eq_comp,
      P.proj_inter, P.proj_congr (Set.inter_eq_left.mpr hBC) _ hB, P.inner_proj]
  rw [norm_sub_sq (𝕜 := ℂ), hinner, P.norm_sq_proj_apply, P.norm_sq_proj_apply]
  simp only [RCLike.re_eq_complex_re, Complex.ofReal_re]
  ring

/-- Appendix A.2: countable additivity of a PVM holds after applying it to
each vector, without an operator-norm additivity or compactness assumption. -/
theorem projectionMeasure_hasSum (P : TauCeti.ProjValMeasure H)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (u : H) :
    HasSum (fun n => P.proj (B n) (hB n) u)
      (P.proj (⋃ n, B n) (MeasurableSet.iUnion hB) u) := by
  classical
  let U : Finset ℕ → Set ℝ := fun s => ⋃ n ∈ s, B n
  have hU (s : Finset ℕ) : MeasurableSet (U s) :=
    MeasurableSet.biUnion (Finset.countable_toSet s) (fun n _ => hB n)
  have hmono : Monotone U := by
    intro s t hst x hx
    simp only [U, Set.mem_iUnion] at hx ⊢
    obtain ⟨n, hn, hxn⟩ := hx
    exact ⟨n, hst hn, hxn⟩
  have htotal : (⋃ s, U s) = ⋃ n, B n := by
    ext x
    simp only [U, Set.mem_iUnion]
    constructor
    · rintro ⟨s, n, _, hx⟩
      exact ⟨n, hx⟩
    · rintro ⟨n, hx⟩
      exact ⟨{n}, n, Finset.mem_singleton_self n, hx⟩
  have hmass : Tendsto (fun s => ((P.diag u) (U s)).toReal) atTop
      (𝓝 (((P.diag u) (⋃ n, B n)).toReal)) := by
    have hm := tendsto_measure_iUnion_atTop (μ := P.diag u) hmono
    rw [htotal] at hm
    exact (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp hm
  have htail : Tendsto (fun s => Real.sqrt
      (((P.diag u) (⋃ n, B n)).toReal - ((P.diag u) (U s)).toReal)) atTop (𝓝 0) := by
    have hdiff := (tendsto_const_nhds (x := ((P.diag u) (⋃ n, B n)).toReal)).sub hmass
    simpa only [Function.comp_def, sub_self, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hdiff
  change Tendsto (fun s : Finset ℕ => ∑ n ∈ s, P.proj (B n) (hB n) u) atTop _
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert htail using 1
  ext s
  have hsub : U s ⊆ ⋃ n, B n := by
    intro x hx
    exact htotal ▸ Set.mem_iUnion.mpr ⟨s, hx⟩
  have hfinite := congrArg (fun A : H →L[ℂ] H => A u) (proj_finset_union P B hB hd s)
  simp only [sum_apply] at hfinite
  rw [← hfinite, ← norm_sq_proj_sub P (hU s) (MeasurableSet.iUnion hB) hsub u,
    Real.sqrt_sq (norm_nonneg _)]

end KVApproximation.Spectral
