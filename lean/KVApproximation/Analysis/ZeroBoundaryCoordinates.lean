module

public import KVApproximation.Analysis.VectorSobolev
public import TauCeti.Analysis.Sobolev.W1p.Zero

/-!
# Scalar coordinates of zero-boundary displacements
-/

public section

open MeasureTheory TopologicalSpace
open scoped Distributions

noncomputable section

namespace KVApproximation.Analysis

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

private theorem compact_coordinate_mem (v : VectorH1 Ω)
    (hv : v ∈ smoothCompactJets Ω) (i : Fin d) :
    v i ∈ TauCeti.w1p0Submodule volume Ω 2 := by
  rcases hv with ⟨φ, hφ, hc, hs, hv⟩
  let L := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i
  let φi : 𝓓(Ω, ℝ) :=
    ⟨L ∘ φ, L.contDiff.comp hφ, hc.comp_left (map_zero L),
      (tsupport_comp_subset (map_zero L) φ).trans hs⟩
  have heq : v i = TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φi := by
    apply TauCeti.W1p.ext_value
    rw [TauCeti.W1p.value_ofTestFunctionₗ]
    apply Lp.ext
    have ht := TauCeti.testFunctionLp_apply_ae (mu := volume) 2 φi
    filter_upwards [hv i, ht] with x hx ht
    exact hx.trans ht.symm
  rw [heq]
  exact TauCeti.W1p.ofTestFunctionₗ_mem_w1p0Submodule φi

private theorem single_test_mem (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    (PiLp.single 2 i (TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ) : VectorH1 Ω)
      ∈ smoothCompactJets Ω := by
  classical
  let I : ℝ →L[ℝ] PhysicalSpace d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i)
  refine ⟨I ∘ φ, I.contDiff.comp φ.contDiff,
    φ.hasCompactSupport.comp_left (map_zero I),
    (tsupport_comp_subset (map_zero I) φ).trans φ.tsupport_subset, ?_⟩
  intro j
  change TauCeti.W1p.value
    ((PiLp.single 2 i (TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ) : VectorH1 Ω) j)
    =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))] fun x => (PiLp.single 2 i (φ x) : PhysicalSpace d) j
  by_cases h : j = i
  · subst j
    simp only [PiLp.single_eq_same, TauCeti.W1p.value_ofTestFunctionₗ]
    exact TauCeti.testFunctionLp_apply_ae (mu := volume) 2 φ
  · simp only [PiLp.single_eq_of_ne 2 h]
    rw [← TauCeti.W1p.valueL_apply, map_zero]
    exact Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (PhysicalSpace d)))

/-- Theorem 3.1, Dirichlet space: the closure of smooth compactly
supported vector jets is exactly the space whose scalar coordinates
belong to the corresponding scalar zero-boundary Sobolev spaces. -/
theorem mem_zeroBoundary_iff (u : VectorH1 Ω) :
    u ∈ zeroBoundarySubmodule Ω ↔
      ∀ i : Fin d, u i ∈ TauCeti.w1p0Submodule volume Ω 2 := by
  classical
  constructor
  · intro hu i
    let P : VectorH1 Ω →L[ℝ] TauCeti.W1p volume Ω 2 :=
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => TauCeti.W1p volume Ω 2) i
    have hle : zeroBoundarySubmodule Ω ≤ (TauCeti.w1p0Submodule volume Ω 2).comap P :=
      Submodule.closure_le.mpr (Submodule.span_le.mpr fun v hv => compact_coordinate_mem v hv i)
    exact hle hu
  · intro hu
    let C := (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d => TauCeti.W1p volume Ω 2)).symm.toContinuousLinearMap
    have hinj (i : Fin d) : C (Pi.single i (u i)) ∈ zeroBoundarySubmodule Ω := by
      let J : TauCeti.W1p volume Ω 2 →L[ℝ] VectorH1 Ω :=
        C.comp (ContinuousLinearMap.single ℝ (fun _ : Fin d => TauCeti.W1p volume Ω 2) i)
      apply TauCeti.w1p0Submodule_subset_of_isClosed
        ((zeroBoundarySubmodule Ω).isClosed.preimage J.continuous) _ (hu i)
      intro φ
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (single_test_mem φ i))
    have hsum : ∑ i, C (Pi.single i (u i)) = u := by
      rw [← map_sum, Finset.univ_sum_single]
      rfl
    rw [← hsum]
    exact (zeroBoundarySubmodule Ω).toSubmodule.sum_mem fun i _ => hinj i

/-- Theorem 3.1, Dirichlet space: a nonempty open domain in positive
physical dimension admits a nonzero zero-boundary displacement. -/
theorem ZeroBoundaryH1.exists_ne_zero
    (hd : 0 < d) (hΩ : (Ω : Set (PhysicalSpace d)).Nonempty) :
    ∃ u : ZeroBoundaryH1 Ω, u ≠ 0 := by
  classical
  obtain ⟨w, hw⟩ := TauCeti.W1p0.exists_value_ne_zero
    (mu := volume) (Omega := Ω) (p := 2) hΩ
  let i : Fin d := ⟨0, hd⟩
  let v : VectorH1 Ω := PiLp.single 2 i (w : TauCeti.W1p volume Ω 2)
  have hv : v ∈ zeroBoundarySubmodule Ω := by
    apply (mem_zeroBoundary_iff v).mpr
    intro j
    change (PiLp.single 2 i (w : TauCeti.W1p volume Ω 2) : VectorH1 Ω) j ∈ _
    by_cases h : j = i
    · subst j
      rw [PiLp.single_eq_same]
      change (w : TauCeti.W1p volume Ω 2) ∈ (TauCeti.w1p0Submodule volume Ω 2).toSubmodule
      exact w.property
    · rw [PiLp.single_eq_of_ne 2 h]
      exact (TauCeti.w1p0Submodule volume Ω 2).zero_mem
  refine ⟨⟨v, hv⟩, ?_⟩
  intro hz
  have hzv : v = 0 := congrArg Subtype.val hz
  have hw0 : (w : TauCeti.W1p volume Ω 2) = 0 := by
    have hi := congrFun (congrArg WithLp.ofLp hzv) i
    simpa only [v, PiLp.single_eq_same, PiLp.zero_apply] using hi
  apply hw
  rw [hw0, ← TauCeti.W1p.valueL_apply, map_zero]

end KVApproximation.Analysis
