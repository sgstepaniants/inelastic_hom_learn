module

public import KVApproximation.Analysis.PeriodicBVTranslation
public import KVApproximation.Analysis.PeriodicCompactness

/-!
# Compactness of bounded periodic variation

The translation estimate gives a uniform L¹ modulus. Fréchet–Kolmogorov
provides relative compactness; lower semicontinuity closes the BV sublevel.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Lemma B.2 (`lem:bv_compact`): bounded sublevels of the full periodic BV
norm are compact in L¹ for finite-dimensional real inner-product targets. -/
theorem isCompact_periodicBV_sublevel {C : ENNReal} (hC : C ≠ ⊤) :
    IsCompact {A : Lp F 1 (cellMeasure d) | periodicBVNorm A ≤ C} := by
  let S : Set (Lp F 1 (cellMeasure d)) := {A | periodicBVNorm A ≤ C}
  have hclosed : IsClosed S := by
    apply IsSeqClosed.isClosed
    intro Aseq A hseq hlim
    exact periodicBVNorm_le_of_tendsto_L1 hlim hseq
  have hcompact : IsCompact (closure S) := by
    apply isCompact_closure_of_periodic_translations (by simp) hC
    · intro A hA
      exact (le_add_of_nonneg_right (by positivity : 0 ≤ periodicVariation A)).trans hA
    · intro ε hε
      have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal r * C) (𝓝 0) (𝓝 0) := by
        simpa only [ENNReal.ofReal_zero, zero_mul] using
          ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto 0) (Or.inr hC)
      have hsmall := hlim.eventually_lt_const hε
      obtain ⟨δ, hδ, hδsmall⟩ := Metric.mem_nhds_iff.mp hsmall
      refine ⟨δ, hδ, fun A hA v hv => ?_⟩
      have hvar : periodicVariation A ≤ C :=
        (le_add_of_nonneg_left (by positivity : 0 ≤ eLpNorm A 1 (cellMeasure d))).trans hA
      apply (periodicVariation_translation_bound A v).trans
      apply (mul_le_mul_right hvar (ENNReal.ofReal ‖v‖)).trans
      exact (hδsmall (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
        abs_norm] using hv)).le
  rwa [hclosed.closure_eq] at hcompact

end KVApproximation.Analysis
