module

public import KVApproximation.Tensor.SobolevCompactness
public import KVApproximation.KelvinVoigt.Material

/-!
# Compactness of smoother material classes
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Remark 4.1 (Bounded Variation): smoother viscosity–elasticity pairs
with uniform Sobolev and coefficient bounds have compact closure in the
paper's product L² topology. The two Sobolev exponents may differ. -/
theorem isCompact_closure_sobolev_materials {d : ℕ} {pV pE CV CE : ENNReal}
    {αV βV αE βE : ℝ} {S : Set (Material d)}
    (hpV : 1 ≤ pV) (hpE : 1 ≤ pE)
    (hαV : 0 ≤ αV) (hβV : 0 ≤ βV) (hCV : CV ≠ ⊤)
    (hαE : 0 ≤ αE) (hβE : 0 ≤ βE) (hCE : CE ≠ ⊤)
    (hV : ∀ M ∈ S, MemLp M.1 ⊤ (cellMeasure d) ∧ HasFieldBounds αV βV M.1 ∧
      ∃ G : PeriodicCell d → PiLp 2 (fun _ : Fin d => Elasticity d),
        MemLp G pV (cellMeasure d) ∧ HasPeriodicDistributionalGradient M.1 G ∧
          eLpNorm M.1 pV (cellMeasure d) + eLpNorm G pV (cellMeasure d) ≤ CV)
    (hE : ∀ M ∈ S, MemLp M.2 ⊤ (cellMeasure d) ∧ HasFieldBounds αE βE M.2 ∧
      ∃ G : PeriodicCell d → PiLp 2 (fun _ : Fin d => Elasticity d),
        MemLp G pE (cellMeasure d) ∧ HasPeriodicDistributionalGradient M.2 G ∧
          eLpNorm M.2 pE (cellMeasure d) + eLpNorm G pE (cellMeasure d) ≤ CE) :
    IsCompact (closure S) := by
  have hVC : IsCompact (closure (Prod.fst '' S)) :=
    isCompact_closure_sobolev_coefficients hpV hαV hβV hCV (by
      rintro A ⟨M, hM, rfl⟩
      exact hV M hM)
  have hEC : IsCompact (closure (Prod.snd '' S)) :=
    isCompact_closure_sobolev_coefficients hpE hαE hβE hCE (by
      rintro A ⟨M, hM, rfl⟩
      exact hE M hM)
  apply (hVC.prod hEC).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hVC.prod hEC).isClosed
  intro M hM
  exact ⟨subset_closure ⟨M, hM, rfl⟩, subset_closure ⟨M, hM, rfl⟩⟩

/-- Remark 4.1 (Bounded Variation): closed smoother material classes with
uniform Sobolev and coefficient bounds are compact in the product L² topology. -/
theorem isCompact_sobolev_materials_of_isClosed {d : ℕ} {pV pE CV CE : ENNReal}
    {αV βV αE βE : ℝ} {S : Set (Material d)}
    (hpV : 1 ≤ pV) (hpE : 1 ≤ pE)
    (hαV : 0 ≤ αV) (hβV : 0 ≤ βV) (hCV : CV ≠ ⊤)
    (hαE : 0 ≤ αE) (hβE : 0 ≤ βE) (hCE : CE ≠ ⊤)
    (hV : ∀ M ∈ S, MemLp M.1 ⊤ (cellMeasure d) ∧ HasFieldBounds αV βV M.1 ∧
      ∃ G : PeriodicCell d → PiLp 2 (fun _ : Fin d => Elasticity d),
        MemLp G pV (cellMeasure d) ∧ HasPeriodicDistributionalGradient M.1 G ∧
          eLpNorm M.1 pV (cellMeasure d) + eLpNorm G pV (cellMeasure d) ≤ CV)
    (hE : ∀ M ∈ S, MemLp M.2 ⊤ (cellMeasure d) ∧ HasFieldBounds αE βE M.2 ∧
      ∃ G : PeriodicCell d → PiLp 2 (fun _ : Fin d => Elasticity d),
        MemLp G pE (cellMeasure d) ∧ HasPeriodicDistributionalGradient M.2 G ∧
          eLpNorm M.2 pE (cellMeasure d) + eLpNorm G pE (cellMeasure d) ≤ CE)
    (hclosed : IsClosed S) : IsCompact S := by
  simpa only [hclosed.closure_eq] using
    isCompact_closure_sobolev_materials hpV hpE hαV hβV hCV hαE hβE hCE hV hE

end KVApproximation.KelvinVoigt
