module

public import KVApproximation.Analysis.PeriodicVariation

/-!
# Distributional gradients on the periodic cell
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

/-- Remark 4.1 (Bounded Variation): the integration-by-parts identity for a
periodic distributional gradient, tested against all C¹ periodic vector
fields. Integrability is supplied separately in the Sobolev applications.
The gradient fibre has the Euclidean sum norm with the inner product on `F`. -/
def HasPeriodicDistributionalGradient {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : PeriodicCell d → F) (G : PeriodicCell d → PiLp 2 (fun _ : Fin d => F)) : Prop :=
  ∀ φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F)),
    (∫ y, ⟪A y, φ.divergence y⟫_ℝ ∂cellMeasure d) =
      -(∫ y, ⟪G y, φ.value y⟫_ℝ ∂cellMeasure d)

end KVApproximation.Analysis
