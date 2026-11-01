module

public import KVApproximation.Analysis.DirichletFields
public import KVApproximation.Analysis.ZeroBoundaryCoordinates
public import TauCeti.Analysis.Sobolev.RellichKondrachov
public import Mathlib.Topology.Sequences

/-!
# Compactness of zero-boundary displacements

Scalar Dirichlet compactness transfers through the finite physical coordinates
and their L² isometry. Weak H¹ convergence identifies the strong L² cluster
points without requiring regularity of the boundary.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped Topology InnerProductSpace

namespace KVApproximation.Analysis

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup

private theorem compact_pi {ι H G : Type*} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : ι → H →L[ℝ] G) (hT : ∀ i, IsCompactOperator (T i)) :
    IsCompactOperator (ContinuousLinearMap.pi T) := by
  classical
  have hK (i : ι) : ∃ K : Set G, IsCompact K ∧
      (T i) '' Metric.ball (0 : H) 1 ⊆ K :=
    (hT i).image_ball_subset_compact (f := (T i).toLinearMap) 1
  choose K hcompact hsubset using hK
  refine ⟨Set.univ.pi K, isCompact_univ_pi hcompact, ?_⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) zero_lt_one)
  intro u hu i _
  exact hsubset i ⟨u, hu, rfl⟩

private theorem compact_closure_image {H G : Type*}
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : H →L[ℝ] G) (hT : IsCompactOperator T)
    {S : Set H} (hS : Bornology.IsBounded S) :
    IsCompact (closure (T '' S)) :=
  hT.isCompact_closure_image_of_bounded (f := T.toLinearMap) hS

private theorem compact_assemble {ι H F G E : Type*} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : F →L[ℝ] G) (C : (ι → E) →L[ℝ] F) (T : ι → H →L[ℝ] E)
    (hT : ∀ i, IsCompactOperator (T i)) :
    IsCompactOperator (U.comp (C.comp (ContinuousLinearMap.pi T))) :=
  ((compact_pi T hT).clm_comp C).clm_comp U

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

private def dirichletCoordinate (i : Fin d) :
    ZeroBoundaryH1 Ω →L[ℝ] TauCeti.W1p0 volume Ω 2 :=
  ContinuousLinearMap.codRestrict
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => TauCeti.W1p volume Ω 2) i).comp
      (zeroBoundarySubmodule Ω).toSubmodule.subtypeL)
    (TauCeti.w1p0Submodule volume Ω 2).toSubmodule
    (fun u => (mem_zeroBoundary_iff u.val).mp u.property i)

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, static homogenization: on every bounded open domain,
the actual value map from vector H¹₀ to vector L² is compact. -/
theorem ZeroBoundaryH1.isCompactOperator_valueL
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    IsCompactOperator (ZeroBoundaryH1.valueL Ω) := by
  let U := (lp_finite_coordinates (E := fun _ : Fin d => ℝ)
    (volume.restrict (Ω : Set (PhysicalSpace d)))).choose
  let C := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ω : Set (PhysicalSpace d))))).symm.toContinuousLinearMap
  let T (i : Fin d) : ZeroBoundaryH1 Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (PhysicalSpace d))) :=
    TauCeti.W1p0.valueL.comp (dirichletCoordinate (Ω := Ω) i)
  have hT (i : Fin d) : IsCompactOperator (T i) := by
    have hs := TauCeti.W1p0.isCompactOperator_valueL (mu := volume) (Omega := Ω)
      (p := 2) (by norm_num) hΩ
    have h := hs.comp_clm (dirichletCoordinate (Ω := Ω) i)
    exact h
  have heq : U.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (C.comp (ContinuousLinearMap.pi T)) = ZeroBoundaryH1.valueL Ω := by
    apply ContinuousLinearMap.ext
    intro u
    change U (C (fun i => T i u)) =
      U (C (fun i => TauCeti.W1p.valueL ((u : VectorH1 Ω) i)))
    apply congrArg U
    apply congrArg C
    funext i
    simp only [T, ContinuousLinearMap.comp_apply, TauCeti.W1p0.valueL_apply,
      TauCeti.W1p.valueL_apply]
    rfl
  have hc := compact_assemble (ι := Fin d) (H := ZeroBoundaryH1 Ω)
    (F := PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ω : Set (PhysicalSpace d)))))
    (G := Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    (E := Lp ℝ 2 (volume.restrict (Ω : Set (PhysicalSpace d))))
    U.toContinuousLinearEquiv.toContinuousLinearMap C T hT
  exact heq ▸ hc

set_option maxHeartbeats 1000000 in
/-- Theorem 3.1, static homogenization: an H¹-bounded set of
zero-boundary displacements has relatively compact L² values. -/
theorem ZeroBoundaryH1.isCompact_closure_value_image
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {S : Set (ZeroBoundaryH1 Ω)} (hS : Bornology.IsBounded S) :
    IsCompact (closure ((ZeroBoundaryH1.valueL Ω) '' S)) := by
  have hcompact := ZeroBoundaryH1.isCompactOperator_valueL (Ω := Ω) hΩ
  generalize ZeroBoundaryH1.valueL Ω = T at hcompact ⊢
  exact compact_closure_image T hcompact hS

/-- Theorem 3.1, static homogenization: every uniformly H¹-bounded
sequence of zero-boundary displacements has a strongly L²-convergent subsequence. -/
theorem ZeroBoundaryH1.exists_subseq_tendsto_value
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (u : ℕ → ZeroBoundaryH1 Ω) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => ZeroBoundaryH1.valueL Ω (u (φ n))) atTop (𝓝 v) := by
  have hS : Bornology.IsBounded (Set.range u) :=
    isBounded_iff_forall_norm_le.mpr ⟨C, by rintro _ ⟨n, rfl⟩; exact hu n⟩
  obtain ⟨v, _, φ, hφ, hv⟩ :=
    (ZeroBoundaryH1.isCompact_closure_value_image hΩ hS).tendsto_subseq
      (fun n => subset_closure ⟨u n, ⟨n, rfl⟩, rfl⟩)
  exact ⟨v, φ, hφ, hv⟩

/-- Theorem 3.1, static homogenization: a uniformly H¹-bounded
sequence converging weakly in H¹₀ converges strongly in L² to the same displacement. -/
theorem ZeroBoundaryH1.tendsto_value_of_weak
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (u : ℕ → ZeroBoundaryH1 Ω) (uLim : ZeroBoundaryH1 Ω)
    {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ uLim))) :
    Tendsto (fun n => ZeroBoundaryH1.valueL Ω (u n)) atTop
      (𝓝 (ZeroBoundaryH1.valueL Ω uLim)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨v, φ, hφ, hv⟩ :=
    ZeroBoundaryH1.exists_subseq_tendsto_value hΩ (fun n => u (ns n)) (fun n => hu (ns n))
  have heq : v = ZeroBoundaryH1.valueL Ω uLim := by
    apply ext_inner_left ℝ
    intro w
    let L : Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d))) →L[ℝ] ℝ :=
      innerSL ℝ w
    have hstrong := (L.continuous.tendsto v).comp hv
    have hlimit := (hweak (L.comp (ZeroBoundaryH1.valueL Ω))).comp
      (hns.comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique hstrong hlimit
  exact ⟨φ, heq ▸ hv⟩

end KVApproximation.Analysis
