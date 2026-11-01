module

public import KVApproximation.Homogenization.MicroscopicTrajectoryProperties
public import KVApproximation.Homogenization.MicroscopicTimeBounds
public import KVApproximation.Analysis.TimeSobolevHalfLine
public import KVApproximation.Analysis.HalfLineLaplaceProperties

/-!
# Weak compactness of homogeneous microscopic evolutions
-/

public section

noncomputable section

open Filter TopologicalSpace
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, half-line compactness: assemble bounded Sobolev realizations
on all finite horizons before substituting the spatial Dirichlet space. -/
private theorem halfLine_subsequence_from_wellposedness
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : ℝ} (hT : 0 < T) (p : ℕ → ℝ → H)
    (P : ∀ S : ℝ, 0 < S → ℕ → TimeH1 H S → Prop)
    (hex : ∀ (S : ℝ) (hS : 0 < S) (n : ℕ), ∃! z, P S hS n z)
    (hbound : ∀ (S : ℝ) (hS : 0 < S), ∃ D : ℝ,
      ∀ n z, P S hS n z → ‖z‖ ≤ D)
    (htrace : ∀ (S : ℝ) (hS : 0 < S) (n : ℕ) (z : TimeH1 H S),
      P S hS n z → ∀ t : Set.Icc (0 : ℝ) S,
        TimeH1.trace (H := H) hS z t = p n t)
    (u : ℕ → TimeH1 H T) (hu : ∀ n, P T hT n (u n))
    {M : ℝ} (hvalue : ∀ n t, 0 ≤ t → ‖p n t‖ ≤ M)
    (hlip : ∀ n, LipschitzOnWith (Real.toNNReal M) (p n) (Set.Ici (0 : ℝ))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ uLim : TimeH1 H T, ∃ v : ℝ → H,
      ContinuousOn v (Set.Ici (0 : ℝ)) ∧
      (∃ M : ℝ, 0 ≤ M ∧ (∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M) ∧
        LipschitzOnWith (Real.toNNReal M) v (Set.Ici (0 : ℝ))) ∧
      (∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace (H := H) hT uLim t = v t) ∧
      (∀ ℓ : TimeH1 H T →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim))) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ ℓ : H →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (p (φ n) t)) atTop (𝓝 (ℓ (v t)))) ∧
      ∀ s : ℝ, 0 < s → ∀ ℓ : H →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (halfLineLaplace (p (φ n)) s)) atTop
          (𝓝 (ℓ (halfLineLaplace v s))) := by
  let w (S : ℝ) (hS : 0 < S) (n : ℕ) : TimeH1 H S :=
    (hex S hS n).exists.choose
  have hw (S : ℝ) (hS : 0 < S) (n : ℕ) : P S hS n (w S hS n) :=
    (hex S hS n).exists.choose_spec
  have hreal (n : ℕ) : w T hT n = u n :=
    (hex T hT n).unique (hw T hT n) (hu n)
  have hTk (k : ℕ) : 0 < T + k := add_pos_of_pos_of_nonneg hT (Nat.cast_nonneg k)
  let C (k : ℕ) := (hbound (T + k) (hTk k)).choose
  have hC (k n : ℕ) : ‖w (T + k) (hTk k) n‖ ≤ C k :=
    (hbound (T + k) (hTk k)).choose_spec n _ (hw (T + k) (hTk k) n)
  obtain ⟨φ, hφ, wLim, _, hweak, vLim, hvLip, hvBound, hvTrace, hvPoint⟩ :=
    TimeH1.exists_halfLine_weak_limit (H := H) hT (fun n t => p n t)
      (fun k => w (T + k) (hTk k)) C hC
      (fun n t => hvalue n t t.property) (fun n => (hlip n).to_restrict)
      (fun k n t => htrace (T + k) (hTk k) n _ (hw (T + k) (hTk k) n) t)
  let v (t : ℝ) : H := vLim ⟨max t 0, le_max_right t 0⟩
  have hv (t : ℝ) (ht : 0 ≤ t) : v t = vLim ⟨t, ht⟩ := by
    change vLim ⟨max t 0, _⟩ = vLim ⟨t, _⟩
    congr 1
    exact Subtype.ext (max_eq_left ht)
  have hvLipOn : LipschitzOnWith (Real.toNNReal M) v (Set.Ici (0 : ℝ)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [hv s hs, hv t ht, Subtype.dist_eq] using
      hvLip.dist_le_mul ⟨s, hs⟩ ⟨t, ht⟩
  have hvNorm (t : ℝ) (ht : 0 ≤ t) : ‖v t‖ ≤ M := by
    rw [hv t ht]
    exact hvBound ⟨t, ht⟩
  have hpoint (t : ℝ) (ht : 0 ≤ t) (ℓ : H →L[ℝ] ℝ) :
      Tendsto (fun n => ℓ (p (φ n) t)) atTop (𝓝 (ℓ (v t))) := by
    rw [hv t ht]
    exact hvPoint ⟨t, ht⟩ ℓ
  let target (S : Set.Ioi (0 : ℝ)) : Prop :=
    ∃ z : TimeH1 H S,
      (∀ t : Set.Icc (0 : ℝ) (S : ℝ), TimeH1.trace (H := H) S.property z t = v t) ∧
      ∀ ℓ : TimeH1 H S →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (w S S.property (φ n))) atTop (𝓝 (ℓ z))
  have hzero : target ⟨T + (0 : ℕ), hTk 0⟩ := by
    refine ⟨wLim 0, ?_, hweak 0⟩
    intro t
    exact (hvTrace 0 t).trans (hv t t.property.1).symm
  have htarget : target ⟨T, hT⟩ := by
    have hTzero : (⟨T + (0 : ℕ), hTk 0⟩ : Set.Ioi (0 : ℝ)) = ⟨T, hT⟩ :=
      Subtype.ext (by simp)
    exact (congrArg target hTzero).mp hzero
  obtain ⟨z, hzTrace, hzWeak⟩ := htarget
  have hM : 0 ≤ M := (norm_nonneg (p 0 0)).trans (hvalue 0 0 le_rfl)
  refine ⟨φ, hφ, z, v, hvLipOn.continuousOn, ⟨M, hM, hvNorm, hvLipOn⟩,
    hzTrace, ?_, hpoint, ?_⟩
  · intro ℓ
    simpa only [hreal] using hzWeak ℓ
  · intro s hs ℓ
    exact halfLineLaplace_weak_tendsto (F := H) (fun n => p (φ n)) v
      (fun n => (hlip (φ n)).continuousOn) hvLipOn.continuousOn
      (fun n t ht => hvalue (φ n) t ht) hvNorm hpoint hs ℓ

/-- Theorem 3.1, zero forcing in the finite-time norm estimate. -/
private theorem zero_forcing_bound
    {H F Z : Type*} [SeminormedAddCommGroup H] [SeminormedAddCommGroup F]
    [SeminormedAddCommGroup Z] {D B : ℝ} (hD : 0 ≤ D)
    (q : H) (z : Z) (hq : ‖q‖ ≤ B)
    (h : ‖z‖ ≤ D * (‖q‖ + ‖(0 : F)‖)) : ‖z‖ ≤ D * B := by
  have hz : ‖z‖ ≤ D * ‖q‖ := by
    simpa only [norm_zero, add_zero] using h
  exact hz.trans (mul_le_mul_of_nonneg_left hq hD)

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance MicroscopicCompactness.instNormable :
    IsNormableSpace ℝ (ZeroBoundaryH1 Ω) :=
  ⟨⟨normSeminorm ℝ (ZeroBoundaryH1 Ω), norm_withSeminorms ℝ (ZeroBoundaryH1 Ω)⟩⟩

/-- Theorem 3.1, homogeneous compactness: one finite-horizon bound applies
to every realization of the uniformly bounded initial family. -/
private theorem uniform_zero_forcing_realizations (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (q : ℕ → ZeroBoundaryH1 Ω)
    {B : ℝ} (hq : ∀ n, ‖q n‖ ≤ B) (S : ℝ) (hS : 0 < S) :
    ∃ D : ℝ, ∀ n (z : TimeH1 (ZeroBoundaryH1 Ω) S),
      IsMicroscopicSolution (Ω := Ω) (T := S) hS V E (ε n) (q n) 0 z →
        ‖z‖ ≤ D := by
  have hb := exists_uniform_microscopic_timeH1_bound (Ω := Ω) (T := S) V E hΩ hS
  let D := hb.choose
  have hD : 0 < D := hb.choose_spec.1
  have htime := hb.choose_spec.2
  refine ⟨D * B, ?_⟩
  intro n z hz
  exact zero_forcing_bound (H := ZeroBoundaryH1 Ω) (F := Forcing Ω S)
    (Z := TimeH1 (ZeroBoundaryH1 Ω) S)
    hD.le (q n) z (hq n) (htime (ε n) (hε n) (q n) 0 z hz)

/-- Theorem 3.1, homogeneous compactness: the initial bound supplies one
value and Lipschitz bound for the entire family of half-line trajectories. -/
private theorem uniform_initial_trajectory_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (q : ℕ → ZeroBoundaryH1 Ω)
    {B : ℝ} (hq : ∀ n, ‖q n‖ ≤ B) :
    ∃ M : ℝ,
      (∀ n t, 0 ≤ t →
        ‖microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hε n).ne' (q n) t‖ ≤ M) ∧
      ∀ n, LipschitzOnWith (Real.toNNReal M)
        (microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hε n).ne' (q n))
        (Set.Ici (0 : ℝ)) := by
  have htrajectory := exists_uniform_microscopicTrajectory_bounds (Ω := Ω) V E hΩ
  let C := htrajectory.choose
  have hC : 0 < C := htrajectory.choose_spec.1
  have htrajectoryBounds := htrajectory.choose_spec.2
  refine ⟨C * B, ?_, ?_⟩
  · intro n t ht
    exact ((htrajectoryBounds (ε n) (hε n).ne' (q n)).1 t ht).trans
      (mul_le_mul_of_nonneg_left (hq n) hC.le)
  · intro n
    exact ((htrajectoryBounds (ε n) (hε n).ne' (q n)).2).weaken
      (Real.toNNReal_mono (mul_le_mul_of_nonneg_left (hq n) hC.le))

/-- Theorem 3.1, homogeneous compactness: finite-horizon realizations have
the actual semigroup trace throughout their closed time interval. -/
private theorem zero_forcing_realization_trace (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) (q : ZeroBoundaryH1 Ω) (S : ℝ) (hS : 0 < S)
    (z : TimeH1 (ZeroBoundaryH1 Ω) S)
    (hz : IsMicroscopicSolution (Ω := Ω) (T := S) hS V E ε q 0 z)
    (t : Set.Icc (0 : ℝ) S) :
    TimeH1.trace (H := ZeroBoundaryH1 Ω) hS z t =
      microscopicTrajectory (Ω := Ω) V E hΩ ε hε.ne' q t :=
  microscopic_zero_forcing_trace (Ω := Ω) (T := S) V E hΩ ε hε hS q z hz t

/-- Theorem 3.1, homogeneous compactness: uniformly bounded initial states
give one subsequence of the actual microscopic evolutions converging weakly
in the prescribed finite-time H¹ space, at every nonnegative time, and in
every positive-rate Laplace transform. The limit traces agree at both endpoints.
Elastic and viscous preparation can each supply the initial bound. -/
theorem microscopic_homogeneous_subsequence (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) {T : ℝ} (hT : 0 < T)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (q : ℕ → ZeroBoundaryH1 Ω)
    {B : ℝ} (hq : ∀ n, ‖q n‖ ≤ B)
    (u : ℕ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ n, IsMicroscopicSolution (Ω := Ω) hT V E (ε n) (q n) 0 (u n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ uLim : TimeH1 (ZeroBoundaryH1 Ω) T, ∃ v : ℝ → ZeroBoundaryH1 Ω,
        ContinuousOn v (Set.Ici (0 : ℝ)) ∧
        (∃ M : ℝ, 0 ≤ M ∧ (∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M) ∧
          LipschitzOnWith (Real.toNNReal M) v (Set.Ici (0 : ℝ))) ∧
        (∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace (H := ZeroBoundaryH1 Ω) hT uLim t = v t) ∧
        (∀ ℓ : TimeH1 (ZeroBoundaryH1 Ω) T →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ uLim))) ∧
        (∀ t : ℝ, 0 ≤ t → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (microscopicTrajectory (Ω := Ω) V E hΩ
            (ε (φ n)) (hε (φ n)).ne' (q (φ n)) t)) atTop (𝓝 (ℓ (v t)))) ∧
        ∀ s : ℝ, 0 < s → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (halfLineLaplace (F := ZeroBoundaryH1 Ω) (microscopicTrajectory (Ω := Ω) V E hΩ
            (ε (φ n)) (hε (φ n)).ne' (q (φ n))) s)) atTop
            (𝓝 (ℓ (halfLineLaplace (F := ZeroBoundaryH1 Ω) v s))) := by
  let p (n : ℕ) : ℝ → ZeroBoundaryH1 Ω :=
    microscopicTrajectory (Ω := Ω) V E hΩ (ε n) (hε n).ne' (q n)
  let P : ∀ S : ℝ, 0 < S → ℕ → TimeH1 (ZeroBoundaryH1 Ω) S → Prop :=
    fun S hS n z => IsMicroscopicSolution (Ω := Ω) (T := S) hS V E (ε n) (q n) 0 z
  have htrajectory := uniform_initial_trajectory_bounds (Ω := Ω) V E hΩ ε hε q hq
  let M := htrajectory.choose
  have hpBound : ∀ n t, 0 ≤ t → ‖p n t‖ ≤ M := htrajectory.choose_spec.1
  have hpLip : ∀ n, LipschitzOnWith (Real.toNNReal M) (p n) (Set.Ici (0 : ℝ)) :=
    htrajectory.choose_spec.2
  exact halfLine_subsequence_from_wellposedness (H := ZeroBoundaryH1 Ω) (T := T) (M := M)
    hT p P
    (fun S hS n =>
      microscopic_exists_unique (Ω := Ω) (T := S) V E hΩ (ε n) (hε n) hS (q n) 0)
    (uniform_zero_forcing_realizations (Ω := Ω) V E hΩ ε hε q hq)
    (fun S hS n z hz t =>
      zero_forcing_realization_trace (Ω := Ω) V E hΩ (ε n) (hε n) (q n) S hS z hz t)
    u hu hpBound hpLip

end KVApproximation.Homogenization
