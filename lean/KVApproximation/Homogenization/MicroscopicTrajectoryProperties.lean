module

public import KVApproximation.Homogenization.MicroscopicTrajectory
public import KVApproximation.Homogenization.MicroscopicEvolution
public import KVApproximation.Homogenization.MicroscopicSemigroup
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sobolev traces and uniform regularity of microscopic trajectories
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, homogeneous evolution: specialize Duhamel to zero forcing
before substituting the spatial Sobolev space. -/
private theorem zero_forcing_timeH1_trace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (R : H →L[ℝ] H)
    {T : ℝ} (hT : 0 < T) (q : H) (u : TimeH1 H T)
    (hinit : TimeH1.initial hT u = q)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = -R (TimeH1.value u t)) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT u t = (NormedSpace.exp (-(t : ℝ) • R)) q := by
  have hode' : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = (-R) (TimeH1.value u t) + (0 : H) := by
    simpa only [neg_apply, add_zero] using hode
  have h := Dynamics.linear_timeH1_duhamel (-R) hT (fun _ => (0 : H))
    MemLp.zero' u hode' t
  simpa only [hinit, map_zero, intervalIntegral.integral_zero, add_zero,
    smul_neg, neg_smul] using h

/-- Theorem 3.1, half-line regularity: the mean value estimate turns a
uniform derivative bound into the same Lipschitz constant. -/
private theorem halfLine_lipschitz_of_derivative
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f f' : ℝ → H) {M : ℝ} (hM : 0 ≤ M)
    (hder : ∀ t : ℝ, HasDerivAt f (f' t) t)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f' t‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal M) f (Set.Ici (0 : ℝ)) := by
  apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (hder t).hasDerivWithinAt)
  intro t ht
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM]
  exact hbound t ht

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicTrajectoryProperties.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance MicroscopicTrajectoryProperties.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

local instance MicroscopicTrajectoryProperties.instTopologicalRing :
    IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ)
      (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1, homogeneous compactness: the continuous trace of every
zero-forcing microscopic weak solution is the same global semigroup trajectory. -/
theorem microscopic_zero_forcing_trace (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    (q : ZeroBoundaryH1 Ω) (u : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsMicroscopicSolution hT V E ε q 0 u) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace (H := ZeroBoundaryH1 Ω) hT u t =
      microscopicTrajectory V E hΩ ε hε.ne' q t := by
  let R : ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω := microscopicRelaxation V E hΩ ε hε.ne'
  have hforced := ((microscopic_solution_iff_ode V E hΩ ε hε hT q 0 u).1 hu).2
  have hode : ∀ᵐ s ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity (H := ZeroBoundaryH1 Ω) u s =
        -R (TimeH1.value (H := ZeroBoundaryH1 Ω) u s) := by
    filter_upwards [hforced, Lp.coeFn_zero (SpatialL2 Ω) 2
      (volume.restrict (Set.Ioo 0 T))] with s hs hz
    simpa only [hz, Pi.zero_apply, map_zero, add_zero] using hs
  exact zero_forcing_timeH1_trace (H := ZeroBoundaryH1 Ω) R hT q u hu.1 hode t

/-- Theorem 3.1, uniform half-line compactness: one constant chosen before
scale and initial data bounds the actual trajectory and its Lipschitz constant. -/
theorem exists_uniform_microscopicTrajectory_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0) (q : ZeroBoundaryH1 Ω),
      (∀ t : ℝ, 0 ≤ t → ‖microscopicTrajectory V E hΩ ε hε q t‖ ≤ C * ‖q‖) ∧
      LipschitzOnWith (Real.toNNReal (C * ‖q‖))
        (microscopicTrajectory V E hΩ ε hε q) (Set.Ici (0 : ℝ)) := by
  have hb := exists_uniform_microscopic_semigroup_bounds (Ω := Ω) V E hΩ
  let C := hb.choose
  have hC : 0 < C := hb.choose_spec.1
  have hbounds := hb.choose_spec.2
  refine ⟨C, hC, ?_⟩
  intro ε hε q
  refine ⟨fun t ht => (hbounds ε hε q t ht).1, ?_⟩
  exact halfLine_lipschitz_of_derivative (microscopicTrajectory V E hΩ ε hε q)
    (fun t => -microscopicRelaxation V E hΩ ε hε
      (microscopicTrajectory V E hΩ ε hε q t))
    (mul_nonneg hC.le (norm_nonneg q))
    (microscopic_homogeneous_hasDerivAt V E hΩ ε hε q)
    (fun t ht => (hbounds ε hε q t ht).2)

end KVApproximation.Homogenization
