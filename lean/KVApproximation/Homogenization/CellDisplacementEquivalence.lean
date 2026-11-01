module

public import KVApproximation.Homogenization.CellDisplacement
public import KVApproximation.Homogenization.PeriodicTests
public import KVApproximation.Homogenization.CorrectorTrajectoryMaps
public import KVApproximation.Dynamics.CellEvolutionExistence

/-!
# Equivalence of displacement balance and the strain-corrector evolution
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Dynamics
open KVApproximation.OperatorTheory

namespace KVApproximation.Homogenization

/-- Appendix A.3: static elastic balance is precisely the negative
elastic projection of the macroscopic strain. -/
private theorem prepared_iff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : CoerciveForm H)
    (X : ClosedSubmodule ℝ H) (a : H) (u : X) :
    (∀ ψ : X, A.form (a + (u : H)) ψ = 0) ↔ u = -A.projection X a := by
  constructor
  · intro h
    apply (A.restrict X).eq_of_form_eq
    intro ψ
    have hh := h ψ
    rw [map_add, add_apply] at hh
    change A.form (u : H) ψ = A.form (- (A.projection X a : H)) ψ
    rw [map_neg, neg_apply, form_projection]
    linarith
  · rintro rfl ψ
    have hneg : ((-A.projection X a : X) : H) = -(A.projection X a : H) := rfl
    rw [hneg, ← sub_eq_add_neg]
    exact form_complement_corrector A X a ψ

/-- Appendix A.3: periodic displacement tests give the same elastic preparation. -/
private theorem periodic_prepared_iff {d : ℕ} (E : CoerciveField d)
    (a : Symmetric d) (u : ZeroMeanPeriodicH1 d) (p : correctorSubspace d)
    (hp : (p : StrainField d) = correctorGradientL d u) :
    (∀ φ : PeriodicH1 d, ⟪multiplication E.field
      (constantStrainL d a + correctorGradientL d u),
      PeriodicH1.symmetricGradientL d φ⟫_ℝ = 0) ↔
      p = -E.toForm.projection (correctorSubspace d) (constantStrainL d a) := by
  have hs := periodic_test_iff_corrector_test (d := d)
    (multiplication E.field (constantStrainL d a + correctorGradientL d u))
  have heq := congrArg (fun w : StrainField d =>
    ∀ ψ : correctorSubspace d, E.toForm.form (constantStrainL d a + w) ψ = 0) hp.symm
  exact hs.trans ((iff_of_eq heq).trans
    (prepared_iff E.toForm (correctorSubspace d) (constantStrainL d a) p))

/-- Appendix A.3: the spatial weak equation is unchanged by strain recovery. -/
private theorem periodic_balance_iff {d : ℕ} (V E : CoerciveField d)
    (a b : Symmetric d) (u v : ZeroMeanPeriodicH1 d) (p q : correctorSubspace d)
    (hp : (p : StrainField d) = correctorGradientL d u)
    (hq : (q : StrainField d) = correctorGradientL d v) :
    (∀ φ : PeriodicH1 d, ⟪multiplication V.field
        (constantStrainL d a + correctorGradientL d u) +
      multiplication E.field (constantStrainL d b + correctorGradientL d v),
      PeriodicH1.symmetricGradientL d φ⟫_ℝ = 0) ↔
      ∀ ψ : correctorSubspace d,
        V.toForm.form (constantStrainL d a + (p : StrainField d)) ψ +
          E.toForm.form (constantStrainL d b + (q : StrainField d)) ψ = 0 := by
  refine (periodic_test_iff_corrector_test (d := d) _).trans ?_
  apply forall_congr'
  intro ψ
  have hs := inner_add_left (𝕜 := ℝ)
    (multiplication V.field (constantStrainL d a + correctorGradientL d u))
    (multiplication E.field (constantStrainL d b + correctorGradientL d v))
    (ψ : StrainField d)
  have heq := congrArg₂ (fun w z : StrainField d =>
    V.toForm.form (constantStrainL d a + w) ψ +
      E.toForm.form (constantStrainL d b + z) ψ) hp.symm hq.symm
  exact iff_of_eq (congrArg (fun r : ℝ => r = 0) (hs.trans heq))

/-- Appendix A.3: a bijective correspondence transfers unique solutions. -/
private theorem existsUnique_transfer {U X : Type*} (R : U → X → Prop)
    (P : U → Prop) (Q : X → Prop)
    (forward : ∀ u, ∃! x, R u x) (inverse : ∀ x, ∃! u, R u x)
    (hiff : ∀ u x, R u x → (P u ↔ Q x)) (hQ : ∃! x, Q x) : ∃! u, P u := by
  obtain ⟨x, hx, hxuniq⟩ := hQ
  obtain ⟨u, hu, huuniq⟩ := inverse x
  refine ⟨u, (hiff u x hu).mpr hx, ?_⟩
  intro v hv
  obtain ⟨y, hy, _⟩ := forward v
  have hyx : y = x := hxuniq y ((hiff v y hy).mp hv)
  exact huuniq v (hyx ▸ hy)

/-- Appendix A.3 (`eq:cell_weak`): the actual displacement-valued periodic
PDE is equivalent to the tested strain-corrector evolution, including its
elasticity-prepared initial condition. -/
theorem periodicCellSolution_iff_evolution {d : ℕ} (V E : CoerciveField d)
    {T : ℝ} (hT : 0 < T) (e : TimeH1 (Symmetric d) T)
    (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (η : TimeH1 (correctorSubspace d) T)
    (h : IsDisplacementStrain (d := d) (T := T) χ η) :
    IsPeriodicCellSolution (d := d) (T := T) V E hT e χ ↔
      IsCellEvolution (H := StrainField d) (F := Symmetric d)
        V.toForm E.toForm (correctorSubspace d) (constantStrainL d) hT e η := by
  set_option backward.isDefEq.respectTransparency false in
    have hi := @displacement_strain_trace d T hT χ η h ⟨0, le_rfl, hT.le⟩
    change (TimeH1.initial (H := (correctorSubspace d)) (T := T) hT η :
        StrainField d) =
      correctorGradientL d (TimeH1.initial (H := ZeroMeanPeriodicH1 d) (T := T) hT χ) at hi
    unfold IsPeriodicCellSolution IsCellEvolution
    apply and_congr
    · exact periodic_prepared_iff E
        (TimeH1.initial (H := Symmetric d) (T := T) hT e)
        (TimeH1.initial (H := ZeroMeanPeriodicH1 d) (T := T) hT χ)
        (TimeH1.initial (H := (correctorSubspace d)) (T := T) hT η) hi
    · apply Filter.eventually_congr
      refine (h.1.and h.2).mono ?_
      intro t ht
      have hv := ht.1
      have hd := ht.2
      exact periodic_balance_iff V E
        (TimeH1.velocity (H := Symmetric d) (T := T) e t)
        (TimeH1.value (H := Symmetric d) (T := T) e t)
        (TimeH1.velocity (H := ZeroMeanPeriodicH1 d) (T := T) χ t)
        (TimeH1.value (H := ZeroMeanPeriodicH1 d) (T := T) χ t)
        (TimeH1.velocity (H := (correctorSubspace d)) (T := T) η t)
        (TimeH1.value (H := (correctorSubspace d)) (T := T) η t) hd hv

set_option maxHeartbeats 400000 in
/-- Section 3.1 (`eqns:cell_problem`) and Appendix A.3: the prepared periodic
cell PDE has a unique zero-mean H¹ displacement trajectory for each H¹
macroscopic strain history on a finite positive interval. -/
theorem periodicCellSolution_exists_unique {d : ℕ} (V E : CoerciveField d)
    {T : ℝ} (hT : 0 < T) (e : TimeH1 (Symmetric d) T) :
    ∃! χ : TimeH1 (ZeroMeanPeriodicH1 d) T,
      IsPeriodicCellSolution (d := d) (T := T) V E hT e χ := by
  have hforward := @displacement_strain_exists_unique d T
  have hinverse := @strain_displacement_exists_unique d T
  have hiff := @periodicCellSolution_iff_evolution d V E T hT e
  have he := cell_evolution_exists_unique (H := StrainField d) (F := Symmetric d)
    V.toForm E.toForm (correctorSubspace d) (constantStrainL d) (T := T) hT e
  have h := @existsUnique_transfer (TimeH1 (ZeroMeanPeriodicH1 d) T)
      (TimeH1 (correctorSubspace d) T) (IsDisplacementStrain (d := d) (T := T))
      (IsPeriodicCellSolution (d := d) (T := T) V E hT e)
      (IsCellEvolution (H := StrainField d) (F := Symmetric d)
        V.toForm E.toForm (correctorSubspace d) (constantStrainL d) hT e)
      hforward hinverse hiff he
  exact h

end KVApproximation.Homogenization
