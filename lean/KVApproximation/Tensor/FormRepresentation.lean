module

public import KVApproximation.Tensor.LinearActionIdentities
public import KVApproximation.Tensor.Trace
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Elasticity tensors and symmetric bilinear forms

Appendix A identifies forms on symmetric strains with fourth-order tensors.
Symmetrized coordinate vectors retain all physical indices; their resolution
of the identity accounts for the off-diagonal multiplicities exactly.
-/

public section

noncomputable section

open scoped InnerProductSpace
open scoped Topology

namespace KVApproximation.Tensor

/-- Appendix A.1: the symmetric coordinate vector represents one physical entry. -/
private def coordinateStrain {d : ℕ} (p : Fin d × Fin d) : Symmetric d :=
  ⟨(1 / 2 : ℝ) • (EuclideanSpace.single p 1 + EuclideanSpace.single p.swap 1), by
    intro i j
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, smul_eq_mul]
    have h₁ : ((j, i) = p) ↔ ((i, j) = p.swap) := by
      cases p
      simp only [Prod.mk.injEq, Prod.swap_prod_mk, and_comm]
    have h₂ : ((j, i) = p.swap) ↔ ((i, j) = p) := by
      cases p
      simp only [Prod.mk.injEq, Prod.swap_prod_mk, and_comm]
    simp only [h₁, h₂]
    ring⟩

/-- Appendix A.1: transposed physical entries have the same symmetric coordinate vector. -/
private theorem coordinateStrain_swap {d : ℕ} (p : Fin d × Fin d) :
    coordinateStrain p.swap = coordinateStrain p := by
  apply Subtype.ext
  simp only [coordinateStrain, Prod.swap_swap, add_comm]

/-- Appendix A.1: coordinate evaluation in the inherited Frobenius product. -/
private theorem coordinateStrain_inner {d : ℕ} (p : Fin d × Fin d) (e : Symmetric d) :
    ⟪coordinateStrain p, e⟫_ℝ = e.val p := by
  change ⟪(1 / 2 : ℝ) • (EuclideanSpace.single p 1 + EuclideanSpace.single p.swap 1),
    e.val⟫_ℝ = e.val p
  rw [real_inner_smul_left, inner_add_left, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul]
  have hp : e.val p.swap = e.val p := e.property p.2 p.1
  rw [hp]
  ring

/-- Appendix A.1: the symmetric coordinate vectors resolve every strain exactly. -/
private theorem sum_coordinateStrain {d : ℕ} (e : Symmetric d) :
    ∑ p : Fin d × Fin d, e.val p • coordinateStrain p = e := by
  apply ext_inner_right ℝ
  intro f
  rw [sum_inner]
  change _ = ⟪e.val, f.val⟫_ℝ
  change _ = ∑ p : Fin d × Fin d, f.val p * e.val p
  apply Finset.sum_congr rfl
  intro p _
  calc
    _ = e.val p * ⟪coordinateStrain p, f⟫_ℝ := real_inner_smul_left _ _ _
    _ = _ := by rw [coordinateStrain_inner, mul_comm]

/-- Appendix A.1: testing both slots on coordinate strains recovers a tensor entry. -/
private theorem coordinateStrain_action {d : ℕ} (A : Elasticity d) (p q : Fin d × Fin d) :
    ⟪coordinateStrain p, action A (coordinateStrain q)⟫_ℝ = A.val (p, q) := by
  rw [coordinateStrain_inner]
  change (∑ r : Fin d × Fin d, A.val (p, r) * (coordinateStrain q).val r) = _
  simp only [coordinateStrain, PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hq : A.val (p, q.swap) = A.val (p, q) :=
    (A.property p.1 p.2 q.1 q.2).2.1.symm
  rw [hq]
  ring

/-- Appendix A.1: scalar strain pairings determine all physical tensor entries. -/
theorem eq_of_inner_action_eq {d : ℕ} {A B : Elasticity d}
    (h : ∀ e f : Symmetric d, ⟪e, action A f⟫_ℝ = ⟪e, action B f⟫_ℝ) : A = B := by
  apply Subtype.ext
  apply PiLp.ext
  rintro ⟨p, q⟩
  rw [← coordinateStrain_action A p q, ← coordinateStrain_action B p q]
  exact h _ _

/-- Appendix A.1: continuity of the scalar pairings gives continuity of the
finite-dimensional tensor in the full Frobenius norm. -/
theorem continuous_of_inner_action {d : ℕ} {T : Type*} [TopologicalSpace T]
    (A : T → Elasticity d)
    (h : ∀ e f : Symmetric d, Continuous (fun t => ⟪e, action (A t) f⟫_ℝ)) :
    Continuous A := by
  apply continuous_induced_rng.2
  change Continuous (fun t => WithLp.toLp 2 (fun p => (A t).val p))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  rintro ⟨p, q⟩
  simpa only [coordinateStrain_action] using h (coordinateStrain p) (coordinateStrain q)

/-- Appendix A.2 and Lemma B.5: scalar strain pairings detect tensor convergence. -/
theorem tendsto_of_inner_action {d : ℕ} {T : Type*} {l : Filter T}
    (A : T → Elasticity d) (B : Elasticity d)
    (h : ∀ e f : Symmetric d, Filter.Tendsto (fun t => ⟪e, action (A t) f⟫_ℝ)
      l (𝓝 ⟪e, action B f⟫_ℝ)) : Filter.Tendsto A l (𝓝 B) := by
  apply tendsto_subtype_rng.2
  change Filter.Tendsto (fun t => WithLp.toLp 2 (fun p => (A t).val p)) l (𝓝 B.val)
  apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.2
  rintro ⟨p, q⟩
  simpa only [coordinateStrain_action] using h (coordinateStrain p) (coordinateStrain q)

/-- Appendix A.2: unconditional scalar additivity in every strain pairing
gives unconditional tensor additivity in the Frobenius norm. -/
theorem hasSum_of_inner_action {d : ℕ} {ι : Type*}
    (A : ι → Elasticity d) (B : Elasticity d)
    (h : ∀ e f : Symmetric d, HasSum (fun i => ⟪e, action (A i) f⟫_ℝ)
      ⟪e, action B f⟫_ℝ) : HasSum A B := by
  classical
  change Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, A i) Filter.atTop (𝓝 B)
  apply tendsto_of_inner_action
  intro e f
  let L : Elasticity d →L[ℝ] ℝ := (innerSL ℝ e).comp ((actionL d).flip f)
  have hsum (s : Finset ι) :
      ⟪e, action (∑ i ∈ s, A i) f⟫_ℝ = ∑ i ∈ s, ⟪e, action (A i) f⟫_ℝ :=
    map_sum L _ s
  simp only [hsum]
  exact h e f

/-- Appendix A.1: the physical entries of the tensor are the coordinate tests of the form. -/
private def formTensor {d : ℕ} (B : Symmetric d →L[ℝ] Symmetric d →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) : Elasticity d :=
  ⟨WithLp.toLp 2 (fun p => B (coordinateStrain p.1) (coordinateStrain p.2)), by
    intro i j k l
    change (B (coordinateStrain (i, j)) (coordinateStrain (k, l)) =
        B (coordinateStrain (j, i)) (coordinateStrain (k, l))) ∧
      (B (coordinateStrain (i, j)) (coordinateStrain (k, l)) =
        B (coordinateStrain (i, j)) (coordinateStrain (l, k))) ∧
      (B (coordinateStrain (i, j)) (coordinateStrain (k, l)) =
        B (coordinateStrain (k, l)) (coordinateStrain (i, j)))
    exact ⟨congrArg (fun e => B e (coordinateStrain (k, l)))
        (coordinateStrain_swap (i, j)).symm,
      congrArg (fun e => B (coordinateStrain (i, j)) e)
        (coordinateStrain_swap (k, l)).symm, hB _ _⟩⟩

/-- Appendix A.1: the constructed tensor has exactly the prescribed bilinear pairing. -/
private theorem formTensor_spec {d : ℕ}
    (B : Symmetric d →L[ℝ] Symmetric d →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (e f : Symmetric d) : ⟪e, action (formTensor B hB) f⟫_ℝ = B e f := by
  have hrow (p : Fin d × Fin d) :
      (∑ q : Fin d × Fin d, B (coordinateStrain p) (coordinateStrain q) * f.val q) =
        B (coordinateStrain p) f := by
    calc
      _ = B (coordinateStrain p) (∑ q : Fin d × Fin d, f.val q • coordinateStrain q) := by
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = _ := by rw [sum_coordinateStrain]
  change ⟪e.val, (action (formTensor B hB) f).val⟫_ℝ = _
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ p : Fin d × Fin d,
    (∑ q : Fin d × Fin d, B (coordinateStrain p) (coordinateStrain q) * f.val q) *
      e.val p) = B e f
  simp_rw [hrow]
  calc
    _ = B (∑ p : Fin d × Fin d, e.val p • coordinateStrain p) f := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [sum_coordinateStrain]

/-- Appendix A.1–A.2: every symmetric bilinear form on the strain space
has one elasticity-tensor representative. -/
theorem existsUnique_form_tensor {d : ℕ}
    (B : Symmetric d →L[ℝ] Symmetric d →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) :
    ∃! A : Elasticity d, ∀ u v, ⟪u, action A v⟫_ℝ = B u v := by
  refine ⟨formTensor B hB, formTensor_spec B hB, ?_⟩
  intro A hA
  apply Subtype.ext
  apply PiLp.ext
  rintro ⟨p, q⟩
  exact (coordinateStrain_action A p q).symm.trans (hA _ _)

/-- Appendix A.2: the physical-index trace is the sum over ordered index pairs. -/
private theorem tensorTrace_eq_sum_coordinates {d : ℕ} (A : Elasticity d) :
    tensorTrace A = ∑ p : Fin d × Fin d, A.val (p, p) := by
  rw [Fintype.sum_prod_type]
  rfl

/-- Appendix A.2: the physical-index trace is independent of the orthonormal
basis used to express its diagonal on symmetric strains. -/
theorem tensorTrace_eq_sum {d : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Symmetric d)) (A : Elasticity d) :
    tensorTrace A = ∑ i, ⟪b i, action A (b i)⟫_ℝ := by
  have hdiag (p : Fin d × Fin d) :
      A.val (p, p) = ∑ i, (b i).val p * (action A (b i)).val p := by
    calc
      _ = ⟪coordinateStrain p, actionLinear A
          (∑ i, ⟪b i, coordinateStrain p⟫_ℝ • b i)⟫_ℝ := by
        rw [b.sum_repr']
        exact (coordinateStrain_action A p p).symm
      _ = _ := by
        rw [map_sum, inner_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        calc
          _ = ⟪b i, coordinateStrain p⟫_ℝ *
              ⟪coordinateStrain p, action A (b i)⟫_ℝ := inner_smul_right _ _ _
          _ = _ := by
            rw [real_inner_comm (coordinateStrain p) (b i),
              coordinateStrain_inner, coordinateStrain_inner]
  rw [tensorTrace_eq_sum_coordinates]
  simp_rw [hdiag]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change _ = ∑ p : Fin d × Fin d, (action A (b i)).val p * (b i).val p
  apply Finset.sum_congr rfl
  intro p _
  exact mul_comm _ _

/-- Appendix A.2: positivity bounds the full Frobenius norm by the operator trace. -/
theorem norm_le_tensorTrace {d : ℕ} (A : Elasticity d)
    (hA : ∀ e : Symmetric d, 0 ≤ ⟪e, action A e⟫_ℝ) : ‖A‖ ≤ tensorTrace A := by
  let B : LinearMap.BilinForm ℝ (Symmetric d) :=
    ((innerSL ℝ (E := Symmetric d)).comp (actionL d A)).toLinearMap₁₂
  have hB (e : Symmetric d) : 0 ≤ B e e := by
    change 0 ≤ ⟪action A e, e⟫_ℝ
    rw [real_inner_comm]
    exact hA e
  have hentry (p q : Fin d × Fin d) :
      B (coordinateStrain p) (coordinateStrain q) = A.val (q, p) := by
    change ⟪action A (coordinateStrain p), coordinateStrain q⟫_ℝ = _
    rw [real_inner_comm]
    exact coordinateStrain_action A q p
  have hdiag (p : Fin d × Fin d) : 0 ≤ A.val (p, p) := by
    rw [← hentry]
    exact hB _
  have hCS (p q : Fin d × Fin d) :
      A.val (p, q) ^ 2 ≤ A.val (p, p) * A.val (q, q) := by
    have h := B.apply_mul_apply_le_of_forall_zero_le hB (coordinateStrain p) (coordinateStrain q)
    simp only [hentry] at h
    have hsym : A.val (q, p) = A.val (p, q) :=
      (A.property p.1 p.2 q.1 q.2).2.2.symm
    simpa only [hsym, ← sq] using h
  have htrace : 0 ≤ tensorTrace A := by
    rw [tensorTrace_eq_sum_coordinates]
    exact Finset.sum_nonneg fun p _ => hdiag p
  apply (sq_le_sq₀ (norm_nonneg A) htrace).mp
  calc
    ‖A‖ ^ 2 = ∑ pq : (Fin d × Fin d) × (Fin d × Fin d), A.val pq ^ 2 :=
      EuclideanSpace.real_norm_sq_eq A.val
    _ ≤ ∑ pq : (Fin d × Fin d) × (Fin d × Fin d),
        A.val (pq.1, pq.1) * A.val (pq.2, pq.2) :=
      Finset.sum_le_sum fun pq _ => hCS pq.1 pq.2
    _ = tensorTrace A ^ 2 := by
      rw [Fintype.sum_prod_type, tensorTrace_eq_sum_coordinates, sq]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- Lemma B.2, Frobenius bound: summing squared images of an orthonormal
strain basis gives the full physical-index Frobenius norm. -/
theorem norm_sq_eq_sum_norm_action {d : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (Symmetric d)) (A : Elasticity d) :
    ‖A‖ ^ 2 = ∑ i, ‖action A (b i)‖ ^ 2 := by
  have hentry (p q : Fin d × Fin d) :
      (action A (coordinateStrain p)).val q = A.val (q, p) :=
    (coordinateStrain_inner q _).symm.trans (coordinateStrain_action A q p)
  have hcolumn (p : Fin d × Fin d) :
      (∑ q : Fin d × Fin d, A.val (q, p) ^ 2) =
        ∑ i, (action A (b i)).val p ^ 2 := by
    calc
      _ = ‖action A (coordinateStrain p)‖ ^ 2 := by
        change _ = ‖(action A (coordinateStrain p)).val‖ ^ 2
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [hentry]
      _ = ∑ i, ⟪b i, action A (coordinateStrain p)⟫_ℝ ^ 2 :=
        (b.sum_sq_inner_right _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← action_symmetric, real_inner_comm, coordinateStrain_inner]
  calc
    ‖A‖ ^ 2 = ∑ q : Fin d × Fin d, ∑ p : Fin d × Fin d, A.val (q, p) ^ 2 := by
      change ‖A.val‖ ^ 2 = _
      rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    _ = ∑ p : Fin d × Fin d, ∑ i, (action A (b i)).val p ^ 2 := by
      rw [Finset.sum_comm]
      simp only [hcolumn]
    _ = ∑ i, ‖action A (b i)‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact (EuclideanSpace.real_norm_sq_eq (action A (b i)).val).symm

end KVApproximation.Tensor
