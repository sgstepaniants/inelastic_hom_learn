module

public import KVApproximation.Homogenization.MicroscopicGreenProperties
public import KVApproximation.Analysis.OperatorConvolutionLimits

/-!
# The microscopic Duhamel limit

The common initial semigroup term cancels, and the uniform Green bound
permits passage to the weak limit in the forcing integral.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, forcing integrability: L² data on a finite horizon
are integrable on that horizon, with their prescribed representative. -/
private theorem lp_two_intervalIntegrable {F : Type*} [NormedAddCommGroup F]
    {T : ℝ} (hT : 0 ≤ T) (f : Lp F 2 (volume.restrict (Set.Ioo 0 T))) :
    IntervalIntegrable (fun t => f t) volume 0 T := by
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).2
    ((Lp.memLp f).integrable (by norm_num))

/-- Theorem 3.1, Duhamel domination: extend the operator kernels
continuously to negative times without changing any causal integral. -/
private theorem clamped_operator_convolution_tendsto
    {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (A : ℝ → ℝ → F →L[ℝ] H) (G : ℝ → F →L[ℝ] H) (hG : Continuous G)
    (hbounds : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ,
      (∀ t : ℝ, 0 ≤ t → ‖A ε t‖ ≤ C) ∧
      LipschitzOnWith (Real.toNNReal C) (A ε) (Set.Ici (0 : ℝ)))
    (hweak : ∀ (g : F) (t : ℝ), 0 ≤ t → ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun ε => ℓ (A ε t g)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (G t g))))
    (f : ℝ → F) {T : ℝ} (hf : IntervalIntegrable f volume 0 T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ℓ : H →L[ℝ] ℝ,
      Tendsto (fun ε => ℓ (∫ r in (0 : ℝ)..t, A ε (t - r) (f r)))
        (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (∫ r in (0 : ℝ)..t, G (t - r) (f r)))) := by
  obtain ⟨C, _, hb⟩ := hbounds
  let A' (ε t : ℝ) := A ε (max t 0)
  have hclamp : LipschitzWith 1
      (fun t : ℝ => (⟨max t 0, le_max_right t 0⟩ : Set.Ici (0 : ℝ))) :=
    (LipschitzWith.id.max_const 0).subtype_mk _
  have hcont (ε : ℝ) : Continuous (A' ε) :=
    ((hb ε).2.to_restrict.comp hclamp).continuous
  have hlimit := tendsto_intervalIntegral_of_weak_operator_tendsto A' G hcont hG
    (C := C) (fun ε t _ => (hb ε).1 (max t 0) (le_max_right t 0))
    (fun t ht g ℓ => by simpa only [A', max_eq_left ht] using hweak g t ht ℓ) f hf
  intro t ht ℓ
  apply (hlimit t ht ℓ).congr'
  apply Eventually.of_forall
  intro ε
  apply congrArg ℓ
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Set.Icc (0 : ℝ) t := by
    simpa only [Set.uIcc_of_le ht.1] using hr
  simp only [A', max_eq_left (sub_nonneg.mpr hr'.2)]

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, Duhamel subtraction: the actual homogeneous trace
removes the common initial semigroup term. -/
private theorem microscopic_forcing_trace
    (V E : CoerciveField d) (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : 0 < ε) {T : ℝ} (hT : 0 < T) (f : Forcing Ω T)
    (q : ZeroBoundaryH1 Ω) (u v : TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : IsMicroscopicSolution hT V E ε q f u)
    (hv : IsMicroscopicSolution hT V E ε q 0 v) (t : Set.Icc (0 : ℝ) T) :
    TimeH1.trace hT u t - TimeH1.trace hT v t =
      ∫ r in (0 : ℝ)..(t : ℝ), microscopicGreen (Ω := Ω) V E hΩ ε ((t : ℝ) - r) (f r) := by
  have hd := @microscopic_duhamel d Ω V E hΩ ε hε T hT q f u hu t
  have hz := @microscopic_zero_forcing_trace d Ω V E hΩ ε hε T hT q v hv t
  have hi : (∫ r in (0 : ℝ)..(t : ℝ),
      microscopicTrajectory V E hΩ ε hε.ne'
        (microscopicLoadL V hΩ ε hε.ne' (f r)) ((t : ℝ) - r)) =
      ∫ r in (0 : ℝ)..(t : ℝ), microscopicGreen (Ω := Ω) V E hΩ ε ((t : ℝ) - r) (f r) := by
    apply intervalIntegral.integral_congr
    intro r _
    exact (@microscopicGreen_apply d Ω V E hΩ ε hε.ne' ((t : ℝ) - r) (f r)).symm
  apply sub_eq_iff_eq_add.mpr
  exact (hd.trans (congrArg₂ (· + ·) hz.symm hi)).trans (add_comm _ _)

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), Duhamel limit:
subtracting the microscopic homogeneous solution with the same initial data
leaves a forcing contribution whose traces converge weakly to the Green
convolution. The prescribed L² forcing needs no time continuity. -/
theorem microscopic_forcing_trace_tendsto
    (V E : CoerciveField d) (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {T : ℝ} (hT : 0 < T) (f : Forcing Ω T)
    (q : ℝ → ZeroBoundaryH1 Ω) (u v : ℝ → TimeH1 (ZeroBoundaryH1 Ω) T)
    (hu : ∀ ε : ℝ, 0 < ε → IsMicroscopicSolution hT V E ε (q ε) f (u ε))
    (hv : ∀ ε : ℝ, 0 < ε → IsMicroscopicSolution hT V E ε (q ε) 0 (v ε))
    (G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω) (hG : Continuous G)
    (hweak : ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
      ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (microscopicGreen (Ω := Ω) V E hΩ ε t g))
          (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (G t g)))) :
    ∀ t : Set.Icc (0 : ℝ) T, ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun ε => ℓ (TimeH1.trace hT (u ε) t - TimeH1.trace hT (v ε) t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (ℓ (∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)))) := by
  intro t ℓ
  have hf : IntervalIntegrable (fun t => f t) volume 0 T :=
    lp_two_intervalIntegrable (F := SpatialL2 Ω) hT.le f
  have hlimit :
      Tendsto (fun ε => ℓ (∫ r in (0 : ℝ)..(t : ℝ),
        microscopicGreen (Ω := Ω) V E hΩ ε ((t : ℝ) - r) (f r)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (ℓ (∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)))) :=
    clamped_operator_convolution_tendsto (F := SpatialL2 Ω) (H := ZeroBoundaryH1 Ω)
      (@microscopicGreen d Ω V E hΩ) G hG
      (@exists_uniform_microscopicGreen_bounds d Ω V E hΩ) hweak
      (fun s => f s) hf t t.property ℓ
  exact hlimit.congr' (Filter.Eventually.mono
    (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε) (fun ε hε =>
    congrArg ℓ (@microscopic_forcing_trace d Ω V E hΩ ε hε T hT f (q ε)
      (u ε) (v ε) (hu ε hε) (hv ε hε) t).symm))

end KVApproximation.Homogenization
