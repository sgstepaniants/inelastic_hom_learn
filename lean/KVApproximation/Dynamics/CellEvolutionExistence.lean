module

public import KVApproximation.Dynamics.CellEvolutionAlgebra
public import KVApproximation.Dynamics.LinearTimeSobolev

/-!
# Existence and uniqueness of the cell evolution
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.OperatorTheory

namespace KVApproximation.Dynamics

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Appendix A.3: the cell corrector exists uniquely in the finite-time H¹ space. -/
theorem cell_evolution_exists_unique (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T) :
    ∃! η : TimeH1 X T, IsCellEvolution V E X ι hT e η := by
  let R := relaxation V E X
  let f : ℝ → X := fun t => -V.projection X (ι (TimeH1.velocity e t)) -
    R (E.projection X (ι (TimeH1.value e t)))
  have hf : MemLp f 2 (volume.restrict (Set.Ioo 0 T)) :=
    ((TimeH1.velocity_memLp e).continuousLinearMap_comp ((V.projection X).comp ι)).neg.sub
      ((TimeH1.value_memLp e).continuousLinearMap_comp
        (R.comp ((E.projection X).comp ι)))
  have hiff (η : TimeH1 X T) :
      (TimeH1.initial hT η = -E.projection X (ι (TimeH1.initial hT e)) ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity η t = (-R) (TimeH1.value η t) + f t) ↔
        IsCellEvolution V E X ι hT e η := by
    rw [cell_evolution_iff_ode]
    apply and_congr_right
    intro _
    apply Filter.eventually_congr
    apply Filter.Eventually.of_forall
    intro t
    change (TimeH1.velocity η t = -R (TimeH1.value η t) + f t) ↔
      TimeH1.velocity η t + R (TimeH1.value η t) = f t
    rw [neg_add_eq_sub, eq_sub_iff_add_eq]
  obtain ⟨η, hη, huniq⟩ := linear_timeH1_exists_unique (-R) hT f hf
    (-E.projection X (ι (TimeH1.initial hT e)))
  exact ⟨η, (hiff η).mp hη, fun ζ hζ => huniq ζ ((hiff ζ).mpr hζ)⟩

end KVApproximation.Dynamics
