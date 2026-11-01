module

public import KVApproximation.Dynamics.CellEvolution
public import KVApproximation.OperatorTheory.VariationalIdentities

/-!
# The cell equation and its shifted corrector
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.OperatorTheory

namespace KVApproximation.Dynamics

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace H] in
/-- Appendix A.3: subtraction of correctors agrees with ambient subtraction. -/
private theorem corrector_coe_sub (X : ClosedSubmodule ℝ H) (u v : X) :
    ((u - v : X) : H) = (u : H) - (v : H) := rfl

omit [CompleteSpace H] in
/-- Appendix A.3: negation of a corrector agrees with ambient negation. -/
private theorem corrector_coe_neg (X : ClosedSubmodule ℝ H) (u : X) :
    ((-u : X) : H) = -(u : H) := rfl

/-- Appendix A.3, passage from `eq:cell_weak` to `eq:cell_ode`:
the two tested expressions agree by the defining variational identities. -/
private theorem cell_equation_iff (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (a b : H) (u v : X) :
    (∀ ψ : X, V.form (a + (u : H)) ψ + E.form (b + (v : H)) ψ = 0) ↔
      u + relaxation V E X v = -V.projection X a - relaxation V E X (E.projection X b) := by
  have heq (ψ : X) :
      (V.restrict X).form (u + relaxation V E X v) ψ -
        (V.restrict X).form (-V.projection X a - relaxation V E X (E.projection X b)) ψ =
          V.form (a + (u : H)) ψ + E.form (b + (v : H)) ψ := by
    change V.form ((u + relaxation V E X v : X) : H) ψ -
      V.form ((-V.projection X a - relaxation V E X (E.projection X b) : X) : H) ψ = _
    simp only [AddMemClass.coe_add, corrector_coe_sub, corrector_coe_neg,
      map_add, map_sub, map_neg, add_apply,
      sub_apply, neg_apply,
      relaxation_spec, form_projection]
    ring
  constructor
  · intro h
    apply (V.restrict X).eq_of_form_eq
    intro ψ
    exact sub_eq_zero.mp ((heq ψ).trans (h ψ))
  · intro h ψ
    rw [← heq ψ, h, sub_self]

/-- Appendix A.3 (`eq:cell_ode`): the tested cell equation is equivalent
to the bounded-operator ODE with its prepared initial condition. -/
theorem cell_evolution_iff_ode (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T)
    (η : TimeH1 X T) :
    IsCellEvolution V E X ι hT e η ↔
      TimeH1.initial hT η = -E.projection X (ι (TimeH1.initial hT e)) ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity (H := X) η t + relaxation V E X (TimeH1.value (H := X) η t) =
            -V.projection X (ι (TimeH1.velocity e t)) -
              relaxation V E X (E.projection X (ι (TimeH1.value e t))) := by
  unfold IsCellEvolution
  apply and_congr_right
  intro _
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall (fun t => cell_equation_iff V E X
    (ι (TimeH1.velocity e t)) (ι (TimeH1.value e t))
    (TimeH1.velocity (H := X) η t) (TimeH1.value (H := X) η t))

/-- Appendix A.3: the change of variable `ω = η + P_E e` isolates the mismatch forcing. -/
theorem cell_evolution_shifted_ode (V E : CoerciveForm H) (X : ClosedSubmodule ℝ H)
    (ι : F →L[ℝ] H) {T : ℝ} (hT : 0 < T) (e : TimeH1 F T)
    (η : TimeH1 X T) (hη : IsCellEvolution V E X ι hT e η) :
    TimeH1.initial hT η + E.projection X (ι (TimeH1.initial hT e)) = 0 ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        TimeH1.velocity (H := X) η t + E.projection X (ι (TimeH1.velocity e t)) +
          relaxation V E X (TimeH1.value (H := X) η t + E.projection X (ι (TimeH1.value e t))) =
            -mismatch V E X (ι (TimeH1.velocity e t)) := by
  obtain ⟨hi, hode⟩ := (cell_evolution_iff_ode V E X ι hT e η).mp hη
  refine ⟨by rw [hi, neg_add_cancel], ?_⟩
  filter_upwards [hode] with t ht
  simp only [map_add, mismatch, sub_apply]
  calc
    _ = (TimeH1.velocity (H := X) η t + relaxation V E X (TimeH1.value (H := X) η t)) +
        (E.projection X (ι (TimeH1.velocity e t)) +
          relaxation V E X (E.projection X (ι (TimeH1.value e t)))) := by abel
    _ = _ := by rw [ht]; abel

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
              (TimeH1.value (H := X) η t + E.projection X (ι (TimeH1.value e t))) := by
  have hode := ((cell_evolution_iff_ode V E X ι hT e η).mp hη).2
  filter_upwards [hode] with t ht
  intro a
  let ω := TimeH1.value (H := X) η t + E.projection X (ι (TimeH1.value e t))
  have hv : TimeH1.velocity (H := X) η t = -V.projection X (ι (TimeH1.velocity e t)) -
      relaxation V E X ω := by
    dsimp only [ω]
    rw [map_add]
    calc
      _ = (TimeH1.velocity (H := X) η t + relaxation V E X (TimeH1.value (H := X) η t)) -
          relaxation V E X (TimeH1.value (H := X) η t) := by abel
      _ = _ := by rw [ht]; abel
  have hvalue : TimeH1.value (H := X) η t = ω - E.projection X (ι (TimeH1.value e t)) := by
    dsimp only [ω]
    abel
  have hV : V.form (ι a) (relaxation V E X ω) =
      V.form (relaxation V E X (V.projection X (ι a))) ω := by
    rw [relaxation_selfAdjoint, form_projection]
  have hE : E.form (ι a) ω = V.form (relaxation V E X (E.projection X (ι a))) ω := by
    rw [relaxation_spec, form_projection]
  have hrem : -V.form (ι a) (relaxation V E X ω) + E.form (ι a) ω =
      -V.form (relaxation V E X (mismatch V E X (ι a))) ω := by
    rw [hV, hE]
    simp only [mismatch, sub_apply, map_sub,
      corrector_coe_sub]
    ring
  calc
    cellStressPairing V E X ι e η t a =
        V.homogenizedForm X ι a (TimeH1.velocity e t) +
          E.homogenizedForm X ι a (TimeH1.value e t) +
            (-V.form (ι a) (relaxation V E X ω) + E.form (ι a) ω) := by
      change V.form (ι a) (ι (TimeH1.velocity e t) + (TimeH1.velocity (H := X) η t : H)) +
          E.form (ι a) (ι (TimeH1.value e t) + (TimeH1.value (H := X) η t : H)) =
        V.form (ι a) (V.complement X (ι (TimeH1.velocity e t))) +
          E.form (ι a) (E.complement X (ι (TimeH1.value e t))) + _
      rw [hv, hvalue]
      simp only [complement_apply, corrector_coe_sub, corrector_coe_neg,
        map_add, map_sub, map_neg]
      ring
    _ = _ := by rw [hrem]; rfl

end KVApproximation.Dynamics
