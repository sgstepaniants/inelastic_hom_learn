module

public import KVApproximation.Homogenization.StaticCellFlux
public import KVApproximation.Homogenization.CorrectorDisplacement
public import KVApproximation.Homogenization.PeriodicTests
public import KVApproximation.OperatorTheory.VariationalIdentities

/-!
# Static corrector displacements and stresses

The weighted projection supplies the periodic strain correction. Its
orthogonality is the cell equilibrium equation, and the mean flux is
the effective constitutive form.
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Theorem 3.1, static cell corrector: the negative weighted projection
is the symmetric gradient of a unique zero-mean periodic H¹ displacement. -/
theorem exists_unique_static_corrector {d : ℕ} (A : CoerciveField d) (e : Symmetric d) :
    ∃! u : ZeroMeanPeriodicH1 d,
      correctorGradientL d u = -(cellProjection A (constantStrainL d e) : StrainField d) := by
  obtain ⟨L, hL, _⟩ := correctorGradient_equiv_exists d
  let η := cellProjection A (constantStrainL d e)
  have hu : correctorGradientL d (L.symm (-η)) = -(η : StrainField d) :=
    (hL (L.symm (-η))).symm.trans (congrArg Subtype.val (L.apply_symm_apply (-η)))
  refine ⟨L.symm (-η), hu, ?_⟩
  intro v hv
  exact correctorGradient_injective d (hv.trans hu.symm)

/-- Theorem 3.1, static oscillating fluxes: the L² flux is represented
by the pointwise coefficient action on the corrected strain. -/
theorem cellFlux_apply_ae {d : ℕ} (A : CoerciveField d) (e : Symmetric d) :
    cellFlux A e =ᵐ[cellMeasure d] fun y =>
      action (A.field y) (e - (cellProjection A (constantStrainL d e) : StrainField d) y) := by
  let η : StrainField d := cellProjection A (constantStrainL d e)
  filter_upwards [multiplication_apply_ae A.field (constantStrainL d e - η),
    Lp.coeFn_sub (constantStrainL d e) η, Lp.coeFn_const 2 (cellMeasure d) e]
    with y hm hs hc
  change multiplication A.field (constantStrainL d e - η) y = _
  rw [hm, hs]
  change action (A.field y) ((Lp.const 2 (cellMeasure d) e) y - η y) = _
  rw [hc]
  rfl

/-- Theorem 3.1, static oscillating fluxes: the cell flux annihilates
every periodic displacement strain. -/
theorem cellFlux_orthogonal_periodic {d : ℕ} (A : CoerciveField d) (e : Symmetric d)
    (w : PeriodicH1 d) :
    ⟪cellFlux A e, PeriodicH1.symmetricGradientL d w⟫_ℝ = 0 := by
  apply (periodic_test_iff_corrector_test (cellFlux A e)).mpr ?_ w
  intro η
  change A.toForm.form
    (A.toForm.complement (correctorSubspace d) (constantStrainL d e)) η = 0
  exact form_complement_corrector A.toForm (correctorSubspace d) (constantStrainL d e) η

/-- Theorem 3.1 (`eq:homogenized_tensors`): the mean corrected stress
represents the static effective form. -/
theorem cellFlux_mean_pairing {d : ℕ} (A : CoerciveField d) (e f : Symmetric d) :
    ⟪e, ∫ y, cellFlux A f y ∂cellMeasure d⟫_ℝ = effectiveForm A e f := by
  have hp : ⟪cellFlux A f, constantStrainL d e⟫_ℝ = effectiveForm A e f := by
    change A.toForm.form
      (A.toForm.complement (correctorSubspace d) (constantStrainL d f)) (constantStrainL d e) =
        A.toForm.form (constantStrainL d e)
          (A.toForm.complement (correctorSubspace d) (constantStrainL d f))
    exact A.toForm.symmetric _ _
  calc
    _ = ∫ y, ⟪e, cellFlux A f y⟫_ℝ ∂cellMeasure d :=
      (integral_inner ((Lp.memLp (cellFlux A f)).integrable (by norm_num)) e).symm
    _ = ⟪constantStrainL d e, cellFlux A f⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 (cellMeasure d) e] with y hy
      change ⟪e, cellFlux A f y⟫_ℝ = ⟪(Lp.const 2 (cellMeasure d) e) y, cellFlux A f y⟫_ℝ
      rw [hy]
      rfl
    _ = _ := by
      rw [real_inner_comm (cellFlux A f) (constantStrainL d e)]
      exact hp

end KVApproximation.Homogenization
