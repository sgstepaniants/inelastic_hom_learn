module

public import KVApproximation.Analysis.TimeSobolev
public import KVApproximation.OperatorTheory.MemoryKernel

/-!
# Evolution of the cell corrector
-/

@[expose] public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.OperatorTheory

namespace KVApproximation.Dynamics

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Appendix A.3 (`eq:cell_weak`): the tested cell equation and its
elasticity-prepared initial corrector, on an arbitrary finite time interval. -/
def IsCellEvolution (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T)
    (η : TimeH1 X T) : Prop :=
  TimeH1.initial hT η = -E.projection X (ι (TimeH1.initial hT e)) ∧
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ ψ : X,
      V.form (ι (TimeH1.velocity e t) + (TimeH1.velocity (H := X) η t : H)) ψ +
        E.form (ι (TimeH1.value e t) + (TimeH1.value (H := X) η t : H)) ψ = 0

/-- Appendix A.3 (`eq:stress_decomp`): the macroscopic stress tested against
a macroscopic strain, before eliminating the microscopic corrector. -/
def cellStressPairing (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (e : TimeH1 F T) (η : TimeH1 X T)
    (t : ℝ) (a : F) : ℝ :=
  V.form (ι a) (ι (TimeH1.velocity e t) + (TimeH1.velocity (H := X) η t : H)) +
    E.form (ι a) (ι (TimeH1.value e t) + (TimeH1.value (H := X) η t : H))

end KVApproximation.Dynamics
