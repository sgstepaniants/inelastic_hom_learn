module

public import KVApproximation.Homogenization.SpatialEvolutionOperators
public import KVApproximation.Homogenization.SpatialStress
public import KVApproximation.OperatorTheory.CoerciveSolverProperties

/-!
# Actual spatial evolution and uniform operator bounds
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance spatialEvolutionNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) :=
  { (inferInstance : SeminormedAddCommGroup (ZeroBoundaryH1 Ω)) with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Theorem 3.1, microscopic forms: the coercive spatial form equals
the actual periodically rescaled weak form. -/
theorem periodicSpatialForm_apply (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0)
    (u v : ZeroBoundaryH1 Ω) :
    (periodicSpatialForm A hΩ ε hε).form u v =
      spatialForm (rescalePeriodic A.field ε) u v := by
  change boundedSpatialForm (rescaledCoefficient Ω A.field ε hε) u v = _
  rw [boundedSpatialForm_apply, spatialForm_rescaledCoefficient]

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, uniform microscopic energy bounds: positive lower and
upper constants can be chosen before every nonzero rescaling. -/
theorem exists_uniform_periodicSpatialForm_bounds (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ (ε : ℝ) (hε : ε ≠ 0),
      (periodicSpatialForm A hΩ ε hε).HasBounds α β := by
  obtain ⟨K, hK, hKorn⟩ := ZeroBoundaryH1.exists_korn_constant hΩ
  refine ⟨A.lower / K ^ 2, ‖A.field‖ + 1,
    div_pos A.lower_pos (pow_pos hK 2), by positivity, ?_⟩
  intro ε hε u
  let B := rescaledCoefficient Ω A.field ε hε
  have hB : ∀ᵐ x ∂volume.restrict (Ω : Set (PhysicalSpace d)), ∀ e : Symmetric d,
      A.lower * ‖e‖ ^ 2 ≤ ⟪e, action (B x) e⟫_ℝ :=
    (hasBounds_rescaledCoefficient_ae Ω A.field ε hε A.bounds).mono
      fun _ hx e => (hx e).1
  constructor
  · have hs := pow_le_pow_left₀ (norm_nonneg u) (hKorn u) 2
    rw [mul_pow] at hs
    calc
      (A.lower / K ^ 2) * ‖u‖ ^ 2 ≤
          (A.lower / K ^ 2) * (K ^ 2 * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hs (div_nonneg A.lower_pos.le (sq_nonneg K))
      _ = A.lower * ‖VectorH1.symmetricGradientL Ω u.val‖ ^ 2 := by
        rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hK.ne')]
      _ ≤ spatialForm B u u := spatialForm_lower_bound B hB u
      _ = (periodicSpatialForm A hΩ ε hε).form u u :=
        (boundedSpatialForm_apply B u u).symm
  · have hstress : ‖spatialStressL B u‖ ≤ ‖A.field‖ * ‖u‖ :=
      (norm_spatialStressL_le B u).trans
        (mul_le_mul_of_nonneg_right (norm_rescaledCoefficient_le Ω A.field ε hε)
          (norm_nonneg u))
    have hstrain : ‖VectorH1.symmetricGradientL Ω u.val‖ ≤ ‖u‖ :=
      (VectorH1.norm_symmetricGradientL_le u.val).trans (VectorH1.norm_gradientL_le u.val)
    change ⟪spatialStressL B u, VectorH1.symmetricGradientL Ω u.val⟫_ℝ ≤ _
    calc
      _ ≤ ‖spatialStressL B u‖ * ‖VectorH1.symmetricGradientL Ω u.val‖ :=
        real_inner_le_norm (spatialStressL B u) (VectorH1.symmetricGradientL Ω u.val)
      _ ≤ (‖A.field‖ * ‖u‖) * ‖u‖ :=
        mul_le_mul hstress hstrain (norm_nonneg (VectorH1.symmetricGradientL Ω u.val))
          (mul_nonneg (norm_nonneg A.field) (norm_nonneg u))
      _ = ‖A.field‖ * ‖u‖ ^ 2 := by ring
      _ ≤ (‖A.field‖ + 1) * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖u‖)

/-- Theorem 3.1, homogeneous microscopic evolution: the generator
represents the actual elastic form in the actual viscous pairing. -/
theorem microscopicRelaxation_spec (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0)
    (u v : ZeroBoundaryH1 Ω) :
    spatialForm (rescalePeriodic V.field ε) (microscopicRelaxation V E hΩ ε hε u) v =
      spatialForm (rescalePeriodic E.field ε) u v := by
  calc
    _ = (periodicSpatialForm V hΩ ε hε).form (microscopicRelaxation V E hΩ ε hε u) v :=
      (periodicSpatialForm_apply V hΩ ε hε _ v).symm
    _ = (periodicSpatialForm E hΩ ε hε).form u v :=
      relativeRiesz_spec (periodicSpatialForm V hΩ ε hε) (periodicSpatialForm E hΩ ε hε) u v
    _ = _ := periodicSpatialForm_apply E hΩ ε hε u v

/-- Theorem 3.1, viscous preparation for Duhamel's formula: the
continuous load map solves the actual viscous elliptic equation. -/
theorem microscopicLoadL_spec (V : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0)
    (f : SpatialL2 Ω) (v : ZeroBoundaryH1 Ω) :
    spatialForm (rescalePeriodic V.field ε) (microscopicLoadL V hΩ ε hε f) v =
      loadPairing f v := by
  rw [← periodicSpatialForm_apply V hΩ ε hε]
  change (periodicSpatialForm V hΩ ε hε).form
    ((periodicSpatialForm V hΩ ε hε).solveL (spatialLoadOperator (Ω := Ω) f)) v = _
  rw [CoerciveForm.solveL_spec, spatialLoadOperator_apply]

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, uniform evolution operators: one constant bounds
the microscopic generator and viscous load map before choosing the scale. -/
theorem exists_uniform_microscopic_operator_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0),
      (∀ u : ZeroBoundaryH1 Ω, ‖microscopicRelaxation V E hΩ ε hε u‖ ≤ C * ‖u‖) ∧
      (∀ f : SpatialL2 Ω, ‖microscopicLoadL V hΩ ε hε f‖ ≤ C * ‖f‖) := by
  obtain ⟨αV, βV, hαV, _, hV⟩ := exists_uniform_periodicSpatialForm_bounds V hΩ
  obtain ⟨αE, βE, _, hβE, hE⟩ := exists_uniform_periodicSpatialForm_bounds E hΩ
  refine ⟨(βE + 1) / αV, div_pos (by linarith) hαV, ?_⟩
  intro ε hε
  have hR := relativeRiesz_opNorm_le (periodicSpatialForm V hΩ ε hε)
    (periodicSpatialForm E hΩ ε hε) hαV hβE.le
    (fun u => (hV ε hε u).1) (fun u => (hE ε hε u).2)
  constructor
  · intro u
    exact ((relativeRiesz _ _).le_of_opNorm_le hR u).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) hαV.le) (norm_nonneg u))
  · intro f
    calc
      ‖microscopicLoadL V hΩ ε hε f‖ ≤ ‖spatialLoadOperator (Ω := Ω) f‖ / αV :=
        (periodicSpatialForm V hΩ ε hε).norm_solveL_le hαV (fun u => (hV ε hε u).1) _
      _ ≤ ‖f‖ / αV :=
        div_le_div_of_nonneg_right (norm_spatialLoadOperator_apply_le f) hαV.le
      _ = (1 / αV) * ‖f‖ := by ring
      _ ≤ ((βE + 1) / αV) * ‖f‖ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) hαV.le) (norm_nonneg f)

end KVApproximation.Homogenization
