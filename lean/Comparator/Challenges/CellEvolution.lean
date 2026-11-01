module

public import KVApproximation.Dynamics.CellEvolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The direct cell derivation of the constitutive law
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.OperatorTheory

namespace KVApproximation.Dynamics

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Appendix A.3 (`eq:cell_ode`): the tested cell equation is equivalent
to the bounded-operator ODE with its prepared initial condition. -/
theorem cell_evolution_iff_ode (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T)
    (η : TimeH1 X T) :
    IsCellEvolution V E X ι hT e η ↔
      TimeH1.initial hT η = -E.projection X (ι (TimeH1.initial hT e)) ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity η t + relaxation V E X (TimeH1.value η t) =
            -V.projection X (ι (TimeH1.velocity e t)) -
              relaxation V E X (E.projection X (ι (TimeH1.value e t))) := by
  sorry

/-- Appendix A.3: the cell corrector exists uniquely in the finite-time H¹ space. -/
theorem cell_evolution_exists_unique (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T) :
    ∃! η : TimeH1 X T, IsCellEvolution V E X ι hT e η := by
  sorry

/-- Appendix A.3: the change of variable `ω = η + P_E e` isolates the mismatch forcing. -/
theorem cell_evolution_shifted_ode (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T)
    (η : TimeH1 X T) (hη : IsCellEvolution V E X ι hT e η) :
    TimeH1.initial hT η + E.projection X (ι (TimeH1.initial hT e)) = 0 ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        TimeH1.velocity η t + E.projection X (ι (TimeH1.velocity e t)) +
          relaxation V E X (TimeH1.value η t + E.projection X (ι (TimeH1.value e t))) =
            -mismatch V E X (ι (TimeH1.velocity e t)) := by
  sorry

/-- Appendix A.3 (`eq:eta_sol`): variation of constants for the shifted corrector,
using its continuous trace at every time in the closed interval. -/
theorem cell_evolution_duhamel (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T)
    (η : TimeH1 X T) (hη : IsCellEvolution V E X ι hT e η)
    (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT η t + E.projection X (ι (TimeH1.trace hT e t)) =
      -(∫ s in (0 : ℝ)..(t : ℝ),
        relaxationSemigroup V E X (t - s) (mismatch V E X (ι (TimeH1.velocity e s)))) := by
  sorry

/-- Appendix A.3 (`eq:stress_decomp`): the residual stress is the negative
viscous pairing of `R D` with the shifted corrector. -/
theorem cell_evolution_stress_remainder (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    (e : TimeH1 F T) (η : TimeH1 X T)
    (hη : IsCellEvolution V E X ι hT e η) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ a : F,
      cellStressPairing V E X ι e η t a =
        V.homogenizedForm X ι a (TimeH1.velocity e t) +
          E.homogenizedForm X ι a (TimeH1.value e t) -
            V.form (relaxation V E X (mismatch V E X (ι a)))
              (TimeH1.value η t + E.projection X (ι (TimeH1.value e t))) := by
  sorry

/-- Appendix A.3 and Remark 3.2: the direct cell derivation yields the same
instantaneous tensors and memory convolution as the homogenization theorem. -/
theorem cell_evolution_constitutive_law (V E : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T)
    (e : TimeH1 F T) (η : TimeH1 X T)
    (hη : IsCellEvolution V E X ι hT e η) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ a : F,
      cellStressPairing V E X ι e η t a =
        V.homogenizedForm X ι a (TimeH1.velocity e t) +
          E.homogenizedForm X ι a (TimeH1.value e t) +
            ∫ s in (0 : ℝ)..t, memoryForm V E X ι (t - s) a (TimeH1.velocity e s) := by
  sorry

end KVApproximation.Dynamics
