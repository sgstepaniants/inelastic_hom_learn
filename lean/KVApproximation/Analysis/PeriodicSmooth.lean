module

public import KVApproximation.Analysis.PeriodicCell
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Differentiation of periodic fields
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Analysis

/-- Sections 3.1 and 4.1: a continuously differentiable periodic field,
expressed through its lift to Euclidean space. -/
structure PeriodicC1 (d : ℕ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  value : PeriodicCell d → F
  contDiff_lift : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin d) => value (toCell x))

/-- Sections 3.1 and 4.1: a coordinate derivative of a periodic field. -/
def PeriodicC1.partial {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : PeriodicC1 d F) (j : Fin d) (y : PeriodicCell d) : F :=
  fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => φ.value (toCell x))
    (cellRepresentative y) (WithLp.toLp 2 (Pi.single j (1 : ℝ)))

end KVApproximation.Analysis
