module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import KVApproximation.KelvinVoigt.PronyProblem

/-!
# Neural approximation from a continuous Prony family
-/

public section

open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

/-- Theorem 4.4, Appendix B.3 and Remark 4.6: a continuous Prony family
with positive shared rates and a strict uniform stress-error gap admits
the paper's neural response construction without adding states. -/
theorem continuous_prony_neural_approximation
    {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
    {αV βV γV αE βE γE δ ε rateLower : ℝ}
    (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
    (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE)
    (hδ : 0 < δ) (hε : 0 < ε)
    (C : CellFamily d αV βV γV αE βE γE hαV hαE)
    {n : ℕ} (hn : 0 < n)
    (P : PronyModel (admissibleMaterials d αV βV γV αE βE γE) (Symmetric d) n)
    (hV : Continuous P.viscosity) (hE : Continuous P.elasticity)
    (hcoef : ∀ k, Continuous (P.coefficient k))
    (hrateLower : 0 < rateLower) (hrate : ∀ k, rateLower ≤ P.rate k)
    (herror : uniformPronyError C P δ < ENNReal.ofReal ε)
    (Fclass : StressResponseClass d (n * strainDimension d))
    (Gclass : KineticResponseClass d (n * strainDimension d))
    (hF : HasUniversalApproximation Fclass) (hG : HasLocallyLipschitzApproximation Gclass) :
    ∃ F ∈ Fclass, ∃ G ∈ Gclass, UniformlyApproximates C F G δ ε := by
  sorry

end KVApproximation.KelvinVoigt
