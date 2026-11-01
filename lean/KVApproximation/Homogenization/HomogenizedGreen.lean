module

public import KVApproximation.Homogenization.GreenUniqueness
public import KVApproximation.Homogenization.MicroscopicGreenProperties
public import KVApproximation.Homogenization.MicroscopicCompactness
public import KVApproximation.Homogenization.HomogeneousLimit
public import KVApproximation.Analysis.HilbertWeakLimits
public import KVApproximation.Analysis.WeakSubsequenceLimit

/-!
# Homogenized Green operators

Viscous preparation gives a constant-load memory balance. Its uniqueness
identifies every microscopic subsequential limit. Weak limits preserve
linearity and the common operator and time-Lipschitz bounds.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology NNReal
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, microscopic family selection: choose solutions before
applying compactness, retaining every pointwise equation. -/
private theorem with_chosen_family {I X : Type*} {P : I → X → Prop} {R : Prop}
    (hex : ∀ i, ∃ x, P i x)
    (next : ∀ u : I → X, (∀ i, P i (u i)) → R) : R := by
  classical
  exact next (fun i => (hex i).choose) (fun i => (hex i).choose_spec)

/-- Theorem 3.1, half-line uniqueness: two conditions on subsequential
limits and their equality at nonnegative times give a whole-family weak limit. -/
private theorem exists_weak_halfLine_limit {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P Q : (ℝ → H) → Prop) (u : ℝ → ℝ → H)
    (hsub : ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] (0 : ℝ)) → (∀ n, 0 < ε n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℝ → H, P v ∧ Q v ∧
        ∀ t : ℝ, 0 ≤ t → ∀ ℓ : H →L[ℝ] ℝ,
          Tendsto (fun n => ℓ (u (ε (φ n)) t)) atTop (𝓝 (ℓ (v t))))
    (hunique : ∀ v w, P v → P w → Q v → Q w → Set.EqOn v w (Set.Ici (0 : ℝ))) :
    ∃ v : ℝ → H, P v ∧ Q v ∧
      ∀ t : ℝ, 0 ≤ t → ∀ ℓ : H →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (u ε t)) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (v t))) := by
  obtain ⟨v, hv, _, hweak⟩ := exists_test_limit_of_unique_test_values
    (fun (j : Set.Ici (0 : ℝ) × (H →L[ℝ] ℝ)) v => j.2 (v j.1))
    (fun v => P v ∧ Q v) u
    (fun ε hε hpos => by
      obtain ⟨φ, hφ, w, hwP, hwQ, hpoint⟩ := hsub ε hε hpos
      exact ⟨φ, hφ, w, ⟨hwP, hwQ⟩, fun j => hpoint j.1 j.1.property j.2⟩)
    (fun v w hv hw j => congrArg j.2
      (hunique v w hv.1 hw.1 hv.2 hw.2 j.1.property))
  exact ⟨v, hv.1, hv.2, fun t ht ℓ => hweak (⟨t, ht⟩, ℓ)⟩

/-- Theorem 3.1, forcing domination: a common half-line operator-norm
Lipschitz bound passes to the weak limit of the constant negative-time extension. -/
private theorem lipschitzWith_of_clamped_weak_operator_limit
    {F H I : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {l : Filter I} [NeBot l] (A : I → ℝ → F →L[ℝ] H)
    (G : ℝ → F →L[ℝ] H) (K : ℝ≥0)
    (hweak : ∀ t g (ℓ : H →L[ℝ] ℝ),
      Tendsto (fun i => ℓ (A i (max t 0) g)) l (𝓝 (ℓ (G t g))))
    (hbound : ∀ i, LipschitzOnWith K (A i) (Set.Ici (0 : ℝ))) :
    LipschitzWith K G := by
  let A' (i : I) (t : ℝ) := A i (max t 0)
  have hclamp : LipschitzWith 1
      (fun t : ℝ => (⟨max t 0, le_max_right t 0⟩ : Set.Ici (0 : ℝ))) :=
    (LipschitzWith.id.max_const 0).subtype_mk _
  have hbound' (i : I) : LipschitzWith K (A' i) := by
    simpa only [A', mul_one, Function.comp_def, Set.domRestrict] using
      (hbound i).to_restrict.comp hclamp
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  apply (G s - G t).opNorm_le_bound (mul_nonneg K.coe_nonneg dist_nonneg)
  intro g
  apply norm_le_of_weak_tendsto (l := l)
    (fun i => (A' i s - A' i t) g) ((G s - G t) g)
  · intro ℓ
    simpa only [A', sub_apply, map_sub] using (hweak s g ℓ).sub (hweak t g ℓ)
  · exact Eventually.of_forall fun i =>
      (A' i s - A' i t).le_of_opNorm_le
        (by simpa only [dist_eq_norm] using (hbound' i).dist_le_mul s t) g

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogenizedGreen.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedGreen.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1, viscous preparation: every positive approach sequence
has a Green subsequence with the actual constant-load memory balance. -/
private theorem microscopicGreen_subsequence
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (g : SpatialL2 Ω)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ))) (hpos : ∀ n, 0 < ε n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℝ → ZeroBoundaryH1 Ω,
      ContinuousOn v (Set.Ici (0 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        constantSpatialFormL (Ω := Ω) C.viscosity (v t) +
          constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, v r) +
          posConvolution C.kernel v (constantSpatialFormL (Ω := Ω)) volume t =
            spatialLoadOperator (Ω := Ω) g) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
        Tendsto (fun n => ℓ (microscopicGreen (Ω := Ω) V E hΩ (ε (φ n)) t g))
          atTop (𝓝 (ℓ (v t))) := by
  let q (n : ℕ) : ZeroBoundaryH1 Ω :=
    microscopicLoadL (Ω := Ω) V hΩ (ε n) (hpos n).ne' g
  have hoperators := exists_uniform_microscopic_operator_bounds (Ω := Ω) V E hΩ
  let B := hoperators.choose
  have hB := hoperators.choose_spec.2
  have hq : ∀ n, ‖q n‖ ≤ B * ‖g‖ := fun n => (hB (ε n) (hpos n).ne').2 g
  have hex (n : ℕ) : ∃ u : TimeH1 (ZeroBoundaryH1 Ω) 1,
      IsMicroscopicSolution (Ω := Ω) (T := 1) zero_lt_one V E (ε n) (q n) 0 u :=
    (microscopic_exists_unique (Ω := Ω) (T := 1)
      V E hΩ (ε n) (hpos n) zero_lt_one (q n) 0).exists
  refine with_chosen_family hex ?_
  intro u hu
  have hcompact := @microscopic_homogeneous_subsequence d Ω V E hΩ 1 zero_lt_one
    ε hpos q (B * ‖g‖) hq u hu
  obtain ⟨φ, hφ, _uLim, v, hv, ⟨M, _hM, hbound, _hLip⟩,
    _htrace, _hweak, hpoint, hLap⟩ := hcompact
  refine ⟨φ, hφ, v, hv, ?_, ?_⟩
  · exact @viscous_limit_green_balance d Ω V E C hΩ
      (fun n => ε (φ n)) (hε.comp hφ.tendsto_atTop) (fun n => hpos (φ n))
      (fun n => q (φ n)) g
      (fun n w => microscopicLoadL_spec (Ω := Ω) V hΩ
        (ε (φ n)) (hpos (φ n)).ne' g w)
      v hv M hbound hLap
  · intro t ht ℓ
    exact (hpoint t ht ℓ).congr' (Eventually.of_forall fun n =>
      congrArg ℓ (@microscopicGreen_apply d Ω V E hΩ
        (ε (φ n)) (hpos (φ n)).ne' t g).symm)

/-- Theorem 3.1, uniqueness of Green limits: every input has one
continuous half-line limit for the entire positive-scale family. -/
private theorem microscopicGreen_weak_limit
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (g : SpatialL2 Ω) :
    ∃ v : ℝ → ZeroBoundaryH1 Ω,
      ContinuousOn v (Set.Ici (0 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        constantSpatialFormL (Ω := Ω) C.viscosity (v t) +
          constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, v r) +
          posConvolution C.kernel v (constantSpatialFormL (Ω := Ω)) volume t =
            spatialLoadOperator (Ω := Ω) g) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
        Tendsto (fun ε => ℓ (microscopicGreen (Ω := Ω) V E hΩ ε t g))
          (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (v t))) := by
  exact exists_weak_halfLine_limit (H := ZeroBoundaryH1 Ω)
    (fun v => ContinuousOn v (Set.Ici (0 : ℝ)))
    (fun v => ∀ t : ℝ, 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (v t) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, v r) +
        posConvolution C.kernel v (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g)
    (fun ε t => microscopicGreen (Ω := Ω) V E hΩ ε t g)
    (fun ε hε hpos => @microscopicGreen_subsequence d Ω V E C hΩ g ε hε hpos)
    (fun v w hv hw hvb hwb => @green_balance_unique d Ω V E C hΩ g v w hv hw hvb hwb)

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), forcing contribution:
the actual microscopic Green operators converge weakly at every nonnegative
time and every spatial L² input to a bounded, time-Lipschitz linear family.
Its constant-load balance uses the actual cell tensors and memory kernel.
The negative-time extension is chosen continuously. -/
theorem exists_homogenizedGreen
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ M : ℝ, 0 < M ∧ ∃ G : ℝ → SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω,
      Continuous G ∧
      (∀ t : ℝ, 0 ≤ t → ‖G t‖ ≤ M) ∧
      LipschitzOnWith (Real.toNNReal M) G (Set.Ici (0 : ℝ)) ∧
      (∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
        constantSpatialFormL (Ω := Ω) C.viscosity (G t g) +
          constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, G r g) +
          posConvolution C.kernel (fun r => G r g)
            (constantSpatialFormL (Ω := Ω)) volume t = spatialLoadOperator (Ω := Ω) g) ∧
      ∀ (g : SpatialL2 Ω) (t : ℝ), 0 ≤ t →
        ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
          Tendsto (fun ε => ℓ (microscopicGreen (Ω := Ω) V E hΩ ε t g))
            (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (G t g))) := by
  let v (g : SpatialL2 Ω) := (microscopicGreen_weak_limit (Ω := Ω) V E C hΩ g).choose
  have hbalance (g : SpatialL2 Ω) :=
    (microscopicGreen_weak_limit (Ω := Ω) V E C hΩ g).choose_spec.2.1
  have hweak (g : SpatialL2 Ω) :=
    (microscopicGreen_weak_limit (Ω := Ω) V E C hΩ g).choose_spec.2.2
  have hboundsExists := exists_uniform_microscopicGreen_bounds (Ω := Ω) V E hΩ
  let M := hboundsExists.choose
  have hM := hboundsExists.choose_spec.1
  have hbounds := hboundsExists.choose_spec.2
  have hoperator (t : ℝ) : ∃ B : SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω,
      (∀ g : SpatialL2 Ω, B g = v g (max t 0)) ∧ ‖B‖ ≤ M :=
    exists_continuousLinearMap_of_weak_tendsto
      (E := SpatialL2 Ω) (H := ZeroBoundaryH1 Ω) (I := ℝ) (C := M)
      (l := 𝓝[>] (0 : ℝ))
      (fun ε => microscopicGreen (Ω := Ω) V E hΩ ε (max t 0))
      (fun g => v g (max t 0))
      (fun g ℓ => hweak g (max t 0) (le_max_right t 0) ℓ)
      (Eventually.of_forall fun ε => (hbounds ε).1 _ (le_max_right t 0))
  refine with_chosen_family hoperator ?_
  intro G hGprops
  have hG (t : ℝ) := (hGprops t).1
  have hnorm (t : ℝ) := (hGprops t).2
  have hpoint (t : ℝ) (g : SpatialL2 Ω) (ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ) :
      Tendsto (fun ε => ℓ (microscopicGreen (Ω := Ω) V E hΩ ε (max t 0) g))
        (𝓝[>] (0 : ℝ)) (𝓝 (ℓ (G t g))) := by
    exact (congrArg
      (fun z : ℝ => Tendsto
        (fun ε => ℓ (microscopicGreen (Ω := Ω) V E hΩ ε (max t 0) g))
        (𝓝[>] (0 : ℝ)) (𝓝 z))
      (congrArg ℓ (hG t g).symm)).mp
        (hweak g (max t 0) (le_max_right t 0) ℓ)
  have hLip : LipschitzWith (Real.toNNReal M) G :=
    lipschitzWith_of_clamped_weak_operator_limit
      (F := SpatialL2 Ω) (H := ZeroBoundaryH1 Ω) (I := ℝ)
      (l := 𝓝[>] (0 : ℝ))
      (fun ε t => microscopicGreen (Ω := Ω) V E hΩ ε t) G
      (Real.toNNReal M) hpoint
      (fun ε => (hbounds ε).2)
  have heq (g : SpatialL2 Ω) (t : ℝ) (ht : 0 ≤ t) : G t g = v g t := by
    simpa only [max_eq_left ht] using hG t g
  refine ⟨M, hM, G, hLip.continuous, fun t _ => hnorm t, hLip.lipschitzOnWith, ?_, ?_⟩
  · intro g t ht
    have hprimitive : (∫ r in (0 : ℝ)..t, G r g) = ∫ r in (0 : ℝ)..t, v g r := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Set.Icc (0 : ℝ) t := by simpa only [Set.uIcc_of_le ht] using hr
      exact heq g r hr'.1
    have hmemory : posConvolution C.kernel (fun r => G r g)
        (constantSpatialFormL (Ω := Ω)) volume t =
          posConvolution C.kernel (v g) (constantSpatialFormL (Ω := Ω)) volume t := by
      exact (posConvolution_eq_integral_sub _ _ _ ht).trans
        ((intervalIntegral.integral_congr fun r hr => by
          have hr' : r ∈ Set.Icc (0 : ℝ) t := by
            simpa only [Set.uIcc_of_le ht] using hr
          exact congrArg (constantSpatialFormL (Ω := Ω) (C.kernel (t - r)))
            (heq g r hr'.1)).trans
          (posConvolution_eq_integral_sub _ _ _ ht).symm)
    exact (congrArg₂ (· + ·)
      (congrArg₂ (· + ·)
        (congrArg (constantSpatialFormL (Ω := Ω) C.viscosity) (heq g t ht))
        (congrArg (constantSpatialFormL (Ω := Ω) C.elasticity) hprimitive))
      hmemory).trans (hbalance g t ht)
  · intro g t ht ℓ
    simpa only [max_eq_left ht] using hpoint t g ℓ

end KVApproximation.Homogenization
