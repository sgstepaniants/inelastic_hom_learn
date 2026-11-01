module

public import KVApproximation.Homogenization.MicroscopicEvolution
public import KVApproximation.Homogenization.MicroscopicSemigroup
public import KVApproximation.Homogenization.PeriodicElliptic
public import KVApproximation.Dynamics.LinearTimeBounds

/-!
# Uniform finite-time bounds for microscopic solutions

The homogeneous semigroup bound and the viscous load map give an H¹
estimate uniform in scale. Elastic preparation controls the initial term.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, forcing estimate: absorb a bounded load map into the
generic finite-time estimate before specializing to spatial Sobolev spaces. -/
private theorem linear_timeH1_load_bound {H F : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : H →L[ℝ] H) (L : F →L[ℝ] H) {T B M : ℝ}
    (hT : 0 < T) (hB : 0 ≤ B) (hM : 0 ≤ M) (hA : ‖A‖ ≤ B)
    (hL : ∀ x : F, ‖L x‖ ≤ B * ‖x‖)
    (hsemigroup : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : H,
      ‖(NormedSpace.exp (s • A)) x‖ ≤ M * ‖x‖)
    (f : Lp F 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + L (f t)) :
    ‖u‖ ≤ ((1 + B) * Real.sqrt T * M) * ‖TimeH1.initial hT u‖ +
      (((1 + B) * Real.sqrt T * M) * Real.sqrt T * B + B) * ‖f‖ := by
  let b := L.compLp f
  have hb : ‖b‖ ≤ B * ‖f‖ :=
    (L.norm_compLp_le f).trans
      (mul_le_mul_of_nonneg_right (L.opNorm_le_bound hB hL) (norm_nonneg f))
  have hode' : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + b t := by
    filter_upwards [hode, L.coeFn_compLp f] with t ht hb_t
    exact ht.trans (congrArg (fun x => A (TimeH1.value u t) + x) hb_t.symm)
  calc
    _ ≤ (1 + ‖A‖) * Real.sqrt T *
        (M * (‖TimeH1.initial hT u‖ + Real.sqrt T * ‖b‖)) + ‖b‖ :=
      Dynamics.linear_timeH1_norm_le A hT hM hsemigroup b u hode'
    _ ≤ (1 + B) * Real.sqrt T *
        (M * (‖TimeH1.initial hT u‖ + Real.sqrt T * (B * ‖f‖))) + B * ‖f‖ := by
      gcongr
    _ = _ := by ring

/-- Theorem 3.1, forcing estimate: normalize the negative generator and
initial trace in the abstract Hilbert space. -/
private theorem negative_linear_timeH1_load_bound {H F : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : H →L[ℝ] H) (L : F →L[ℝ] H) {T B M : ℝ}
    (hT : 0 < T) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hR : ∀ x : H, ‖R x‖ ≤ B * ‖x‖) (hL : ∀ x : F, ‖L x‖ ≤ B * ‖x‖)
    (hsemigroup : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : H,
      ‖(NormedSpace.exp (-s • R)) x‖ ≤ M * ‖x‖)
    (f : Lp F 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (q₀ : H) (hinit : TimeH1.initial hT u = q₀)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = -R (TimeH1.value u t) + L (f t)) :
    ‖u‖ ≤ ((1 + B) * Real.sqrt T * M) * ‖q₀‖ +
      (((1 + B) * Real.sqrt T * M) * Real.sqrt T * B + B) * ‖f‖ := by
  have hA : ‖-R‖ ≤ B := by
    rw [norm_neg]
    exact R.opNorm_le_bound hB hR
  have hs : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : H,
      ‖(NormedSpace.exp (s • (-R))) x‖ ≤ M * ‖x‖ := by
    simpa only [smul_neg, neg_smul] using hsemigroup
  simpa only [hinit] using linear_timeH1_load_bound (-R) L hT hB hM hA hL hs f u hode

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicTimeBounds.instNormedGroup : NormedAddCommGroup (ZeroBoundaryH1 Ω) :=
  inferInstance

local instance MicroscopicTimeBounds.instNormable : IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

local instance MicroscopicTimeBounds.instTopologicalRing :
    IsTopologicalRing (ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (ContinuousLinearMap.toSeminormedRing (𝕜 := ℝ)
      (E := ZeroBoundaryH1 Ω)).toNonUnitalSeminormedRing

/-- Theorem 3.1, finite-time compactness estimate: one positive constant
controls the actual microscopic H¹ trajectory before choosing its scale,
initial displacement or L² forcing. -/
theorem exists_uniform_microscopic_timeH1_bound (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε →
      ∀ (q₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T),
        IsMicroscopicSolution hT V E ε q₀ f u → ‖u‖ ≤ C * (‖q₀‖ + ‖f‖) := by
  have hop := exists_uniform_microscopic_operator_bounds (Ω := Ω) V E hΩ
  let B := hop.choose
  have hB : 0 < B := hop.choose_spec.1
  have hoperators := hop.choose_spec.2
  have hsg := exists_uniform_microscopic_semigroup_bounds (Ω := Ω) V E hΩ
  let M := hsg.choose
  have hM : 0 < M := hsg.choose_spec.1
  have hsemigroup := hsg.choose_spec.2
  let P := (1 + B) * Real.sqrt T * M
  let Q := P * Real.sqrt T * B + B
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨P + Q + 1, by positivity, ?_⟩
  intro ε hε q₀ f u hu
  let R : ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω :=
    microscopicRelaxation V E hΩ ε hε.ne'
  let L : SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω := microscopicLoadL V hΩ ε hε.ne'
  have hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity (H := ZeroBoundaryH1 Ω) u t =
        -R (TimeH1.value (H := ZeroBoundaryH1 Ω) u t) + L (f t) :=
    ((microscopic_solution_iff_ode V E hΩ ε hε hT q₀ f u).1 hu).2
  have hbound : ‖u‖ ≤ P * ‖q₀‖ + Q * ‖f‖ :=
    negative_linear_timeH1_load_bound (H := ZeroBoundaryH1 Ω) (F := SpatialL2 Ω) (T := T)
      R L hT hB.le hM.le (hoperators ε hε.ne').1 (hoperators ε hε.ne').2
      (fun s hs x => (hsemigroup ε hε.ne' x s hs.1).1) f u q₀ hu.1 hode
  calc
    ‖u‖ ≤ P * ‖q₀‖ + Q * ‖f‖ := hbound
    _ ≤ (P + Q + 1) * ‖q₀‖ + (P + Q + 1) * ‖f‖ := by
      gcongr <;> linarith
    _ = _ := by ring

/-- Theorem 3.1, admissible initial conditions: elastic preparation
gives a common finite-time H¹ bound in terms of the fixed initial load and
the time-dependent L² forcing. -/
theorem exists_uniform_prepared_timeH1_bound (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g₀ : SpatialL2 Ω) (u₀ : ℝ → ZeroBoundaryH1 Ω),
      IsPreparedInitialFamily E g₀ u₀ → ∀ (ε : ℝ), 0 < ε →
        ∀ (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T),
          IsMicroscopicSolution hT V E ε (u₀ ε) f u → ‖u‖ ≤ C * (‖g₀‖ + ‖f‖) := by
  have htime := exists_uniform_microscopic_timeH1_bound (Ω := Ω) V E hΩ hT
  let C := htime.choose
  have hC : 0 < C := htime.choose_spec.1
  have htime_bound := htime.choose_spec.2
  have hinitial := periodic_elliptic_uniform_bound (Ω := Ω) E hΩ
  let D := hinitial.choose
  have hD : 0 < D := hinitial.choose_spec.1
  have hinitial_bound := hinitial.choose_spec.2
  refine ⟨C * (D + 1), mul_pos hC (by linarith), ?_⟩
  intro g₀ u₀ hprepared ε hε f u hu
  have hinit : ‖u₀ ε‖ ≤ D * ‖g₀‖ := hinitial_bound ε hε g₀ (u₀ ε) (hprepared ε hε)
  calc
    ‖u‖ ≤ C * (‖u₀ ε‖ + ‖f‖) := htime_bound ε hε (u₀ ε) f u hu
    _ ≤ C * (D * ‖g₀‖ + ‖f‖) := by gcongr
    _ ≤ C * (D + 1) * (‖g₀‖ + ‖f‖) := by
      nlinarith [mul_nonneg (mul_nonneg hC.le hD.le) (norm_nonneg f),
        mul_nonneg hC.le (norm_nonneg g₀)]

end KVApproximation.Homogenization
