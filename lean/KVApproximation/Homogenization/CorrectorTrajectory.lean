module

public import KVApproximation.Analysis.TimeSobolev
public import KVApproximation.Homogenization.CorrectorSpace

/-!
# Periodic displacement and strain trajectories
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Section 3.1 (`eq:strain_corrector`) and Appendix A.3: the strain
corrector and its weak time derivative are the symmetric gradients of
the displacement corrector and its weak time derivative. -/
def IsDisplacementStrain {d : ℕ} {T : ℝ}
    (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (η : TimeH1 (correctorSubspace d) T) : Prop :=
  ((fun t => (TimeH1.value (H := (correctorSubspace d)) (T := T) η t : StrainField d))
    =ᵐ[volume.restrict (Set.Ioo 0 T)] fun t => correctorGradientL d
      (TimeH1.value (H := ZeroMeanPeriodicH1 d) (T := T) χ t)) ∧
  ((fun t => (TimeH1.velocity (H := (correctorSubspace d)) (T := T) η t : StrainField d))
    =ᵐ[volume.restrict (Set.Ioo 0 T)] fun t => correctorGradientL d
      (TimeH1.velocity (H := ZeroMeanPeriodicH1 d) (T := T) χ t))

end KVApproximation.Homogenization
