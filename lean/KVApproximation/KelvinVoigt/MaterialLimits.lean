module

public import KVApproximation.KelvinVoigt.Material
public import KVApproximation.Tensor.FieldStability

/-!
# Limits of admissible materials

The coefficient closure theorem applies separately to viscosity and elasticity.
The L¹, L² and L∞ representatives are related only by almost-everywhere equality.
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Lemma B.2: transfer the L² representatives to L¹, apply coefficient
closedness, and return all three constraints to the original representatives. -/
private theorem coefficient_constraints_of_tendsto
    {d : ℕ} {A : CoefficientField d 2} {Aseq : ℕ → CoefficientField d 2}
    {α β : ℝ} {C : ENNReal} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hseq : ∀ n, MemLp (Aseq n) ⊤ (cellMeasure d) ∧
      HasFieldBounds α β (Aseq n) ∧ periodicBVNorm (Aseq n) ≤ C)
    (hconv : Tendsto
      (fun n => eLpNorm (fun y => Aseq n y - A y) 1 (cellMeasure d)) atTop (𝓝 0)) :
    MemLp A ⊤ (cellMeasure d) ∧ HasFieldBounds α β A ∧ periodicBVNorm A ≤ C := by
  let hA : MemLp A 1 (cellMeasure d) := (Lp.memLp A).mono_exponent (by norm_num)
  let hAs (n : ℕ) : MemLp (Aseq n) 1 (cellMeasure d) :=
    (Lp.memLp (Aseq n)).mono_exponent (by norm_num)
  let B : CoefficientField d 1 := hA.toLp A
  let Bseq (n : ℕ) : CoefficientField d 1 := (hAs n).toLp (Aseq n)
  have hbconv : Tendsto Bseq atTop (𝓝 B) := by
    apply tendsto_iff_dist_tendsto_zero.2
    have heq (n : ℕ) : dist (Bseq n) B =
        (eLpNorm (fun y => Aseq n y - A y) 1 (cellMeasure d)).toReal := by
      rw [Lp.dist_def]
      congr 1
      exact eLpNorm_congr_ae ((hAs n).coeFn_toLp.sub hA.coeFn_toLp)
    simp only [heq]
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hconv
  have hbseq (n : ℕ) : MemLp (Bseq n) ⊤ (cellMeasure d) ∧
      HasFieldBounds α β (Bseq n) ∧ periodicBVNorm (Bseq n) ≤ C := by
    refine ⟨(hseq n).1.ae_eq (hAs n).coeFn_toLp.symm,
      (hseq n).2.1.congr (hAs n).coeFn_toLp.symm, ?_⟩
    rw [periodicBVNorm_congr (hAs n).coeFn_toLp]
    exact (hseq n).2.2
  obtain ⟨hb, hbounds, hBV⟩ := coefficient_constraints_of_tendsto_L1 hα hβ hbseq hbconv
  refine ⟨hb.ae_eq hA.coeFn_toLp, hbounds.congr hA.coeFn_toLp, ?_⟩
  rwa [periodicBVNorm_congr hA.coeFn_toLp] at hBV

/-- Lemma B.2 and Corollary B.4 (`lem:bv_compact`, `cor:continuity_tensors`):
an L¹ limit of admissible materials remains admissible, including its BV bounds.
The ambient L² assumption follows automatically from the common L-infinity bound. -/
theorem admissibleMaterials_mem_of_tendsto_L1 {d : ℕ}
    (_hd : d ∈ ({1, 2, 3} : Set ℕ)) {αV βV γV αE βE γE : ℝ}
    (hαV : 0 < αV) (hV : αV ≤ βV) (_hγV : 0 < γV)
    (hαE : 0 < αE) (hE : αE ≤ βE) (_hγE : 0 < γE)
    {M : Material d} {Mseq : ℕ → Material d}
    (hseq : ∀ n, Mseq n ∈ admissibleMaterials d αV βV γV αE βE γE)
    (hVconv : Tendsto
      (fun n => eLpNorm (fun y => (Mseq n).1 y - M.1 y) 1 (cellMeasure d)) atTop (𝓝 0))
    (hEconv : Tendsto
      (fun n => eLpNorm (fun y => (Mseq n).2 y - M.2 y) 1 (cellMeasure d)) atTop (𝓝 0)) :
    M ∈ admissibleMaterials d αV βV γV αE βE γE := by
  obtain ⟨hVtop, hVbounds, hVBV⟩ := coefficient_constraints_of_tendsto
    hαV.le (hαV.le.trans hV)
    (fun n => ⟨(hseq n).1, (hseq n).2.2.1, (hseq n).2.2.2.2.1⟩) hVconv
  obtain ⟨hEtop, hEbounds, hEBV⟩ := coefficient_constraints_of_tendsto
    hαE.le (hαE.le.trans hE)
    (fun n => ⟨(hseq n).2.1, (hseq n).2.2.2.1, (hseq n).2.2.2.2.2⟩) hEconv
  exact ⟨hVtop, hEtop, hVbounds, hEbounds, hVBV, hEBV⟩

end KVApproximation.KelvinVoigt
