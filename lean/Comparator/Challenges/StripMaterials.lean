module

public import KVApproximation.KelvinVoigt.Material
public import KVApproximation.KelvinVoigt.StripFields

/-!
# A convergent family in one admissible material class
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`), admissibility and convergence:
the identity material and all thin-strip materials belong to one fixed
BV-bounded class and converge in its actual L² topology and both L¹ seminorms. -/
theorem exists_strip_material_family {d : ℕ} (i : Fin d) :
    ∃ M : admissibleMaterials d 1 1 (‖identityElasticity d‖ + 1)
        1 2 (4 * ‖identityElasticity d‖ + 1),
      ∃ Mseq : ℕ → admissibleMaterials d 1 1 (‖identityElasticity d‖ + 1)
          1 2 (4 * ‖identityElasticity d‖ + 1),
        (∀ᵐ y ∂cellMeasure d, M.val.1 y = identityElasticity d ∧
          M.val.2 y = identityElasticity d) ∧
        (∀ n, ∀ᵐ y ∂cellMeasure d,
          (Mseq n).val.1 y = identityElasticity d ∧
            (Mseq n).val.2 y = stripElasticity i n y) ∧
        Tendsto Mseq atTop (𝓝 M) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y)
          1 (cellMeasure d)) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y)
          1 (cellMeasure d)) atTop (𝓝 0) := by
  sorry

end KVApproximation.KelvinVoigt
