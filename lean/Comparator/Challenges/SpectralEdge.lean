module

public import KVApproximation.KelvinVoigt.SpectralEdge

/-!
# Spectral-edge discontinuity
-/

public section

open MeasureTheory Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`): the thin-strip construction
belongs to one BV-bounded material class, converges in both L¹ and L², and has
spectral edge two while the limit has edge one. The final conclusion is failure
of continuity on that actual material class. -/
theorem spectral_edge_discontinuous {d : ℕ} (hd : d = 1 ∨ d = 2 ∨ d = 3) (i : Fin d) :
    ∃ γV γE : ℝ, 0 < γV ∧ 0 < γE ∧
      ∃ M : admissibleMaterials d 1 1 γV 1 2 γE,
      ∃ Mseq : ℕ → admissibleMaterials d 1 1 γV 1 2 γE,
        (∀ᵐ y ∂cellMeasure d, M.val.1 y = identityElasticity d ∧
          M.val.2 y = identityElasticity d) ∧
        (∀ n, ∀ᵐ y ∂cellMeasure d,
          (Mseq n).val.1 y = identityElasticity d ∧
            (Mseq n).val.2 y = stripElasticity i n y) ∧
        Tendsto (fun n => (Mseq n).val) atTop (𝓝 M.val) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y)
          1 (cellMeasure d)) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y)
          1 (cellMeasure d)) atTop (𝓝 0) ∧
        materialSpectralEdge (by norm_num) (by norm_num) M = 1 ∧
        (∀ n, materialSpectralEdge (by norm_num) (by norm_num) (Mseq n) = 2) ∧
        ¬ Continuous (materialSpectralEdge (d := d) (γV := γV) (γE := γE)
          (βV := 1) (βE := 2) (show (0 : ℝ) < 1 by norm_num)
          (show (0 : ℝ) < 1 by norm_num)) := by
  sorry

end KVApproximation.KelvinVoigt
