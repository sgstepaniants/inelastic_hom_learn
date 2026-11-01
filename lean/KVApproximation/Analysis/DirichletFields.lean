module

public import KVApproximation.Analysis.VectorSobolevFields

/-!
# Values of zero-boundary displacements
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace KVApproximation.Analysis

/-- Theorem 3.1, spatial compactness: the actual L² value of a
zero-boundary H¹ displacement. -/
def ZeroBoundaryH1.valueL {d : ℕ} (Ω : Opens (PhysicalSpace d)) :
    ZeroBoundaryH1 Ω →L[ℝ]
      Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
  (VectorH1.valueL Ω).comp (zeroBoundarySubmodule Ω).toSubmodule.subtypeL

end KVApproximation.Analysis
