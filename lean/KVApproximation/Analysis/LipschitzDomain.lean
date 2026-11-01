module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz boundaries in Euclidean space
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Analysis

/-- Theorem 3.1, domain geometry: deletion of a coordinate when expressing
the boundary as a graph. -/
def dropCoordinate {d : ℕ} (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ {j : Fin d // j ≠ i} :=
  WithLp.toLp 2 (fun j => x j.val)

/-- Theorem 3.1: locally, an orthogonal change of coordinates expresses
the material domain as the region above a Lipschitz graph. -/
def HasLipschitzBoundary {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ frontier Ω, ∃ r : ℝ, 0 < r ∧
    ∃ Q : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
    ∃ i : Fin d,
    ∃ g : EuclideanSpace ℝ {j : Fin d // j ≠ i} → ℝ,
    (∃ L : NNReal, LipschitzWith L g) ∧
      ∀ y ∈ Metric.ball x r,
        y ∈ Ω ↔ g (dropCoordinate i (Q (y - x))) < Q (y - x) i

end KVApproximation.Analysis
