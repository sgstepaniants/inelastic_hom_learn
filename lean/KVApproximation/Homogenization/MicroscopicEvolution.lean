module

public import KVApproximation.Homogenization.SpatialEvolutionProperties
public import KVApproximation.Homogenization.WeakProblem
public import KVApproximation.Dynamics.VariationalEvolution

/-!
# Microscopic viscoelastic evolution

The actual spatial weak equation is a bounded linear evolution on the
Dirichlet Hilbert space. Its continuous time trace satisfies Duhamel's
formula with viscously prepared spatial loads.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicEvolution.instNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) :=
  { (inferInstance : SeminormedAddCommGroup (ZeroBoundaryH1 Ω)) with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

local instance MicroscopicEvolution.instNormable : IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

local instance MicroscopicEvolution.instTopologicalRing : IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ) (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1 (`eq:two_scale_weak_form`): the actual microscopic
weak PDE is equivalent to the spatial Hilbert-valued evolution equation,
including its initial trace and common exceptional time set. -/
theorem microscopic_solution_iff_ode (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    (q₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T) :
    IsMicroscopicSolution hT V E ε q₀ f u ↔
      TimeH1.initial (H := ZeroBoundaryH1 Ω) hT u = q₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity (H := ZeroBoundaryH1 Ω) u t =
            -microscopicRelaxation V E hΩ ε hε.ne'
              (TimeH1.value (H := ZeroBoundaryH1 Ω) u t) +
              microscopicLoadL V hΩ ε hε.ne' (f t) := by
  unfold IsMicroscopicSolution
  apply and_congr_right
  intro _
  apply Filter.eventually_congr
  apply Filter.Eventually.of_forall
  intro t
  simpa only [periodicSpatialForm_apply, spatialLoadOperator_apply,
    microscopicRelaxation, microscopicLoadL, ContinuousLinearMap.comp_apply] using
    variational_equation_iff (periodicSpatialForm V hΩ ε hε.ne')
      (periodicSpatialForm E hΩ ε hε.ne')
      (TimeH1.velocity (H := ZeroBoundaryH1 Ω) u t)
      (TimeH1.value (H := ZeroBoundaryH1 Ω) u t) (spatialLoadOperator (Ω := Ω) (f t))

/-- Theorem 3.1, microscopic well-posedness: every positive scale,
Dirichlet initial value and L² forcing give a unique actual weak solution. -/
theorem microscopic_exists_unique (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    (q₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T) :
    ∃! u : TimeH1 (ZeroBoundaryH1 Ω) T,
      IsMicroscopicSolution hT V E ε q₀ f u := by
  let R : ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω := microscopicRelaxation V E hΩ ε hε.ne'
  let b : ℝ → ZeroBoundaryH1 Ω := fun t => microscopicLoadL V hΩ ε hε.ne' (f t)
  have hb : MemLp b 2 (volume.restrict (Set.Ioo 0 T)) :=
    (Lp.memLp f).continuousLinearMap_comp (microscopicLoadL V hΩ ε hε.ne')
  have hex : ∃! u : TimeH1 (ZeroBoundaryH1 Ω) T,
      TimeH1.initial (H := ZeroBoundaryH1 Ω) hT u = q₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          TimeH1.velocity (H := ZeroBoundaryH1 Ω) u t =
            (-R) (TimeH1.value (H := ZeroBoundaryH1 Ω) u t) + b t :=
    Dynamics.linear_timeH1_exists_unique (H := ZeroBoundaryH1 Ω) (T := T) (-R) hT b hb q₀
  let u := hex.exists.choose
  have hu := hex.exists.choose_spec
  refine ⟨u, (microscopic_solution_iff_ode V E hΩ ε hε hT q₀ f u).2 hu, ?_⟩
  intro w hw
  exact hex.unique ((microscopic_solution_iff_ode V E hΩ ε hε hT q₀ f w).1 hw) hu

/-- Theorem 3.1, Duhamel normalization: substitute the initial trace and
normalize the negative generator before specializing to the spatial space. -/
private theorem negative_generator_duhamel {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (R : H →L[ℝ] H)
    {T : ℝ} (hT : 0 < T) (b : ℝ → H)
    (hb : MemLp b 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (q₀ : H) (hinit : TimeH1.initial hT u = q₀)
    (hode : ∀ᵐ s ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u s = (-R) (TimeH1.value u s) + b s) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT u t = (NormedSpace.exp (-(t : ℝ) • R)) q₀ +
      ∫ s in (0 : ℝ)..(t : ℝ), (NormedSpace.exp (-((t : ℝ) - s) • R)) (b s) := by
  simpa only [hinit, smul_neg, neg_smul] using
    Dynamics.linear_timeH1_duhamel (H := H) (T := T) (-R) hT b hb u hode t

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, microscopic Duhamel formula: the actual solution trace
is the homogeneous evolution of its initial value plus viscously prepared forcing. -/
theorem microscopic_duhamel (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T)
    (q₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsMicroscopicSolution hT V E ε q₀ f u) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace (H := ZeroBoundaryH1 Ω) hT u t =
      (NormedSpace.exp (-(t : ℝ) • microscopicRelaxation V E hΩ ε hε.ne')) q₀ +
        ∫ s in (0 : ℝ)..(t : ℝ),
          (NormedSpace.exp (-((t : ℝ) - s) • microscopicRelaxation V E hΩ ε hε.ne'))
            (microscopicLoadL V hΩ ε hε.ne' (f s)) := by
  let R : ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω := microscopicRelaxation V E hΩ ε hε.ne'
  let b : ℝ → ZeroBoundaryH1 Ω := fun s => microscopicLoadL V hΩ ε hε.ne' (f s)
  have hb : MemLp b 2 (volume.restrict (Set.Ioo 0 T)) :=
    (Lp.memLp f).continuousLinearMap_comp (microscopicLoadL V hΩ ε hε.ne')
  have hode : ∀ᵐ s ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity (H := ZeroBoundaryH1 Ω) u s =
        (-R) (TimeH1.value (H := ZeroBoundaryH1 Ω) u s) + b s :=
    ((microscopic_solution_iff_ode V E hΩ ε hε hT q₀ f u).1 hu).2
  exact negative_generator_duhamel (H := ZeroBoundaryH1 Ω) (T := T)
    R hT b hb u q₀ hu.1 hode t

end KVApproximation.Homogenization
