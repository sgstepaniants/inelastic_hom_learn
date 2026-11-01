module

public import KVApproximation.KelvinVoigt.SpectralEdge

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`), limit spectrum:
the actual identity material has upper spectral edge one while retaining
the admissible class's stored elasticity upper bound two. -/
theorem materialSpectralEdge_identity {d : ℕ} (i : Fin d)
    {γV γE : ℝ} (M : admissibleMaterials d 1 1 γV 1 2 γE)
    (hV : M.val.1 =ᵐ[cellMeasure d] fun _ => identityElasticity d)
    (hE : M.val.2 =ᵐ[cellMeasure d] fun _ => identityElasticity d) :
    materialSpectralEdge (by norm_num) (by norm_num) M = 1 := by
  sorry

/-- Proposition 4.7 (`prop:no_spectral_stability`), strip spectrum:
the full relaxation operator for a thin-strip material has upper
spectral edge two, independently of the strip's positive width. -/
theorem materialSpectralEdge_strip {d : ℕ} (i : Fin d) (n : ℕ)
    {γV γE : ℝ} (M : admissibleMaterials d 1 1 γV 1 2 γE)
    (hV : M.val.1 =ᵐ[cellMeasure d] fun _ => identityElasticity d)
    (hE : M.val.2 =ᵐ[cellMeasure d] stripElasticity i n) :
    materialSpectralEdge (by norm_num) (by norm_num) M = 2 := by
  sorry

end KVApproximation.KelvinVoigt
