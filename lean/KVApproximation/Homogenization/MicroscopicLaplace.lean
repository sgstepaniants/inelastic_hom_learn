module

public import KVApproximation.Homogenization.MicroscopicTrajectory
public import KVApproximation.Homogenization.MicroscopicSemigroup
public import KVApproximation.Homogenization.SpatialEvolutionProperties
public import KVApproximation.Analysis.HalfLineLaplaceDerivative

/-!
# Transformed microscopic evolution and prepared data
-/

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory

namespace KVApproximation.Homogenization

/-- Theorem 3.1, homogeneous initial trace: the operator exponential
at zero fixes every initial vector. -/
private theorem exponential_initial_value {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H] (R : H →L[ℝ] H) (q : H) :
    (NormedSpace.exp (-(0 : ℝ) • R)) q = q := by
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, one_apply_eq_self]

/-- Theorem 3.1, Laplace-domain argument: integrate the bounded linear
evolution before substituting the spatial Dirichlet space. -/
private theorem laplace_linear_evolution {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [CompleteSpace H] (R : H →L[ℝ] H) (u : ℝ → H)
    (hu : ContinuousOn u (Set.Ici (0 : ℝ)))
    (hder : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt u (-R (u t)) t)
    {M N : ℝ} (hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖u t‖ ≤ M)
    (hvelocity : ∀ t ∈ Set.Ici (0 : ℝ), ‖-R (u t)‖ ≤ N)
    {s : ℝ} (hs : 0 < s) :
    s • halfLineLaplace u s - u 0 = -R (halfLineLaplace u s) := by
  have hderCont : ContinuousOn (fun t => -R (u t)) (Set.Ici (0 : ℝ)) :=
    (R.continuous.comp_continuousOn hu).neg
  have htransform := halfLineLaplace_derivative u (fun t => -R (u t))
    hu hderCont hder hbound hvelocity hs
  have hint := integrable_halfLineLaplace u hu hbound hs
  have hcomm : halfLineLaplace (fun t => -R (u t)) s = -R (halfLineLaplace u s) := by
    simpa only [halfLineLaplace, neg_apply, map_smul, smul_neg] using
      (-R).integral_comp_comm hint
  exact htransform.symm.trans hcomm

/-- Theorem 3.1, elastic preparation: the transformed velocity is
tested in the combined form, retaining the initial elastic load. -/
private theorem elastic_preparation_form {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (V E : H →L[ℝ] H →L[ℝ] ℝ) (R : H →L[ℝ] H)
    (q L v : H) {s : ℝ} (hs : 0 < s) (g : ℝ)
    (hR : V (R L) v = E L v) (hq : E q v = g)
    (hLap : s • L - q = -R L) :
    V (s • L - q) v + s⁻¹ * E (s • L - q) v = -s⁻¹ * g := by
  have hV : V (s • L - q) v = -E L v := by
    rw [hLap, map_neg, neg_apply, hR]
  have hE : E (s • L - q) v = s * E L v - g := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hq]
  rw [hV, hE, mul_sub, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  ring

/-- Theorem 3.1, viscous preparation: the transformed displacement is
tested in the combined form with the viscous initial load. -/
private theorem viscous_preparation_form {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (V E : H →L[ℝ] H →L[ℝ] ℝ) (R : H →L[ℝ] H)
    (q L v : H) {s : ℝ} (hs : 0 < s) (g : ℝ)
    (hR : V (R L) v = E L v) (hq : V q v = g)
    (hLap : s • L - q = -R L) :
    V L v + s⁻¹ * E L v = s⁻¹ * g := by
  have hV : s * V L v - g = -E L v := by
    calc
      _ = V (s • L - q) v := by
        simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hq]
      _ = -E L v := by rw [hLap, map_neg, neg_apply, hR]
  have hsum : s * V L v + E L v = g := by linarith
  calc
    V L v + s⁻¹ * E L v = s⁻¹ * (s * V L v + E L v) := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    _ = s⁻¹ * g := congrArg (s⁻¹ * ·) hsum

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicLaplace.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance MicroscopicLaplace.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

local instance MicroscopicLaplace.instTopologicalRing :
    IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ)
      (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1, Laplace-domain argument: the transform of the actual
homogeneous trajectory satisfies the spatial relaxation equation. -/
theorem microscopicTrajectory_laplace_equation (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω) {s : ℝ} (hs : 0 < s) :
    s • halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s - q =
      -microscopicRelaxation V E hΩ ε hε
        (halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s) := by
  have hder := microscopic_homogeneous_hasDerivAt V E hΩ ε hε q
  have hb := exists_uniform_microscopic_semigroup_bounds (Ω := Ω) V E hΩ
  have hbounds := hb.choose_spec.2 ε hε q
  have h := laplace_linear_evolution (H := ZeroBoundaryH1 Ω)
    (microscopicRelaxation (Ω := Ω) V E hΩ ε hε)
    (microscopicTrajectory V E hΩ ε hε q)
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t _ => hder t) (fun t ht => (hbounds t ht).1)
    (fun t ht => (hbounds t ht).2) hs
  have hzero : microscopicTrajectory V E hΩ ε hε q 0 = q :=
    exponential_initial_value (H := ZeroBoundaryH1 Ω)
      (microscopicRelaxation (Ω := Ω) V E hΩ ε hε) q
  simpa only [hzero] using h

/-- Theorem 3.1, elastic preparation: the transformed velocity has
combined viscosity/elasticity form and load -g/s. -/
theorem microscopic_prepared_laplace_form (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic E.field ε) q v = loadPairing g v)
    {s : ℝ} (hs : 0 < s) (v : ZeroBoundaryH1 Ω) :
    let L := halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s
    spatialForm (rescalePeriodic V.field ε) (s • L - q) v +
      s⁻¹ * spatialForm (rescalePeriodic E.field ε) (s • L - q) v =
      -s⁻¹ * loadPairing g v := by
  let L := halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s
  simpa only [periodicSpatialForm_apply] using
    elastic_preparation_form (H := ZeroBoundaryH1 Ω)
      (periodicSpatialForm V hΩ ε hε).form
      (periodicSpatialForm E hΩ ε hε).form (microscopicRelaxation V E hΩ ε hε)
      q L v hs (loadPairing g v)
      (relativeRiesz_spec (periodicSpatialForm V hΩ ε hε)
        (periodicSpatialForm E hΩ ε hε) L v)
      ((periodicSpatialForm_apply E hΩ ε hε q v).trans (hq v))
      (microscopicTrajectory_laplace_equation V E hΩ ε hε q hs)

/-- Theorem 3.1, Duhamel forcing: viscous preparation gives the
combined transformed form with load g/s for the displacement transform. -/
theorem microscopic_viscous_laplace_form (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω) (g : SpatialL2 Ω)
    (hq : ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic V.field ε) q v = loadPairing g v)
    {s : ℝ} (hs : 0 < s) (v : ZeroBoundaryH1 Ω) :
    let L := halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s
    spatialForm (rescalePeriodic V.field ε) L v +
      s⁻¹ * spatialForm (rescalePeriodic E.field ε) L v =
      s⁻¹ * loadPairing g v := by
  let L := halfLineLaplace (microscopicTrajectory V E hΩ ε hε q) s
  simpa only [periodicSpatialForm_apply] using
    viscous_preparation_form (H := ZeroBoundaryH1 Ω)
      (periodicSpatialForm V hΩ ε hε).form
      (periodicSpatialForm E hΩ ε hε).form (microscopicRelaxation V E hΩ ε hε)
      q L v hs (loadPairing g v)
      (relativeRiesz_spec (periodicSpatialForm V hΩ ε hε)
        (periodicSpatialForm E hΩ ε hε) L v)
      ((periodicSpatialForm_apply V hΩ ε hε q v).trans (hq v))
      (microscopicTrajectory_laplace_equation V E hΩ ε hε q hs)

end KVApproximation.Homogenization
