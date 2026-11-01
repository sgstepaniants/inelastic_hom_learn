module

public import KVApproximation.Examples.LinearSurrogate
public import KVApproximation.Tensor.Spaces
public import KVApproximation.Tensor.MandelFiniteIsometry
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import KVApproximation.Dynamics.TrajectoryMaps

/-!
# Changes of coordinates for fitted linear responses
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.Examples.LinearSurrogate

/-- Appendix C.6, full-row-rank argument: a right inverse splits a
surjective linear map into its output and kernel coordinates. -/
private theorem split_surjective {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (hf : Function.Surjective f) :
    ∃ T : V ≃ₗ[ℝ] W × LinearMap.ker f, ∀ v, (T v).1 = f v := by
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hfg (w : W) : f (g w) = w := LinearMap.congr_fun hg w
  let T : V ≃ₗ[ℝ] W × LinearMap.ker f :=
    { toFun := fun v => (f v, ⟨v - g (f v), by simp [LinearMap.mem_ker, hfg]⟩)
      invFun := fun wk => g wk.1 + wk.2
      left_inv := by intro v; dsimp; abel
      right_inv := by
        rintro ⟨w, k⟩
        apply Prod.ext
        · simp [hfg]
        · apply Subtype.ext
          simp [hfg]
      map_add' := by
        intro x y
        apply Prod.ext
        · exact map_add f x y
        · apply Subtype.ext
          dsimp
          simp only [map_add]
          abel
      map_smul' := by
        intro a x
        apply Prod.ext
        · exact map_smul f a x
        · apply Subtype.ext
          dsimp
          simp only [map_smul, smul_sub] }
  exact ⟨T, fun _ => rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Appendix C.6 (`app:kv2d_linear_fit`): a full-row-rank stress map can be
reduced to a sum of tensor blocks by an invertible state-coordinate change.
The fitted affine offsets have already been subtracted. -/
theorem exists_sum_coordinates {n : ℕ} (hn : 0 < n)
    (B : BlockState n E →ₗ[ℝ] E) (hB : Function.Surjective B) :
    ∃ S : BlockState n E ≃ₗ[ℝ] BlockState n E,
      ∀ q : BlockState n E, B (S q) = ∑ i : Fin n, q i := by
  classical
  let L : BlockState n E →ₗ[ℝ] E :=
    { toFun := fun q => ∑ i : Fin n, q i
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum] }
  have hL : Function.Surjective L := by
    intro y
    refine ⟨blockInsertion ⟨0, hn⟩ y, ?_⟩
    change (∑ i : Fin n, Pi.single ⟨0, hn⟩ y i) = y
    simp
  obtain ⟨TB, hTB⟩ := split_surjective B hB
  obtain ⟨TL, hTL⟩ := split_surjective L hL
  have hdim : Module.finrank ℝ (LinearMap.ker L) = Module.finrank ℝ (LinearMap.ker B) := by
    have hb := TB.finrank_eq
    have hl := TL.finrank_eq
    rw [Module.finrank_prod] at hb hl
    omega
  let K : LinearMap.ker L ≃ₗ[ℝ] LinearMap.ker B := LinearEquiv.ofFinrankEq _ _ hdim
  let U := (LinearEquiv.refl ℝ E).prodCongr K
  refine ⟨TL.trans (U.trans TB.symm), ?_⟩
  intro q
  change B (TB.symm (U (TL q))) = _
  rw [← hTB]
  simp only [LinearEquiv.apply_symm_apply, U, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]
  exact hTL q

/-- Appendix C.6: the full-row-rank scalar fit admits the stated sum
coordinates under the prescribed strain and block Mandel maps. -/
theorem mandel_sum_coordinates {d n : ℕ} (hn : 0 < n)
    (B : EuclideanSpace ℝ (Fin (n * KVApproximation.Tensor.strainDimension d)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (KVApproximation.Tensor.strainDimension d)))
    (hB : Function.Surjective B) :
    ∃ S : EuclideanSpace ℝ (Fin (n * KVApproximation.Tensor.strainDimension d)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (n * KVApproximation.Tensor.strainDimension d)),
      ∀ q : BlockState n (KVApproximation.Tensor.Symmetric d),
        B (S (KVApproximation.Tensor.scalarBlockStrainMandel q)) =
          KVApproximation.Tensor.scalarStrainMandel (∑ i : Fin n, q i) := by
  obtain ⟨U, hU⟩ := KVApproximation.Tensor.scalarStrainMandel_isometry d
  obtain ⟨T, hT⟩ := KVApproximation.Tensor.scalarBlockStrainMandel_isometry n d
  let B0 := U.symm.toLinearEquiv.toLinearMap.comp (B.comp T.toLinearEquiv.toLinearMap)
  have hB0 : Function.Surjective B0 := U.symm.surjective.comp (hB.comp T.surjective)
  obtain ⟨S, hS⟩ := exists_sum_coordinates hn B0 hB0
  refine ⟨T.symm.toLinearEquiv.trans (S.trans T.toLinearEquiv), ?_⟩
  intro q
  rw [← hT, ← hU]
  change B (T (S (T.symm (T q)))) = U (∑ i, q i)
  rw [T.symm_apply_apply]
  apply U.symm.injective
  rw [U.symm_apply_apply]
  exact hS q

/-- Appendix C.6 (`app:kv2d_linear_fit`): transforming the state transports
the input and evolution maps to `S⁻¹ C` and `S⁻¹ D S`. These fitted maps are
arbitrary linear maps; no symmetry or dissipativity is asserted. -/
theorem transformed_kinetics {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E)
    (C : E →ₗ[ℝ] BlockState n E) (D : BlockState n E →ₗ[ℝ] BlockState n E)
    (v : E) (q : BlockState n E) :
    S.symm (C v + D (S q)) = (S.symm.toLinearMap.comp C) v +
      (S.symm.toLinearMap.comp (D.comp S.toLinearMap)) q := by
  exact map_add S.symm _ _

/-- Appendix C.6 and Section 5.1 (`eqns:learned_fitted_dynamics`): the
transformed kinetic equation is the stated sum of input and evolution blocks. -/
theorem transformed_kinetic_blocks {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E)
    (C : E →ₗ[ℝ] BlockState n E) (D : BlockState n E →ₗ[ℝ] BlockState n E)
    (v : E) (q : BlockState n E) (i : Fin n) :
    (S.symm (C v + D (S q))) i = inputBlock S C i v +
      ∑ j : Fin n, evolutionBlock S D i j (q j) := by
  classical
  have hsum : q = ∑ j : Fin n, blockInsertion j (q j) := by
    ext i
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    change q i = ∑ j : Fin n, Pi.single j (q j) i
    simp [Pi.single_apply]
  have h := congrArg (fun z => (S.symm (D (S z))) i) hsum
  simp only [map_sum, WithLp.ofLp_sum, Finset.sum_apply] at h
  rw [map_add, PiLp.add_apply]
  change (S.symm (C v)) i + (S.symm (D (S q))) i = _
  rw [h]
  rfl

/-- Appendix C.6 and Section 5.1: the full stress formula retains both
instantaneous terms and replaces the state term by the sum of tensor blocks. -/
theorem transformed_stress {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E) (B : BlockState n E →ₗ[ℝ] E)
    (hBS : ∀ q : BlockState n E, B (S q) = ∑ i : Fin n, q i)
    (Av Ae : E →ₗ[ℝ] E) (v e : E) (q : BlockState n E) :
    Av v + Ae e + B (S q) = Av v + Ae e + ∑ i : Fin n, q i := by
  rw [hBS]

/-- Appendix C.6: the constant invertible coordinate change transports
bounded Sobolev trajectories and their velocities, including the initial state. -/
theorem trajectory_coordinates [CompleteSpace E] {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E) (ξ : BoundedTrajectory (BlockState n E)) :
    ∃ q : BoundedTrajectory (BlockState n E),
      (∀ t : ℝ, q.value t = S.symm (ξ.value t)) ∧
      (q.velocity =ᵐ[timeMeasure] fun t => S.symm (ξ.velocity t)) ∧
      (ξ.value 0 = 0 → q.value 0 = 0) := by
  let A := S.symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨ξ.map A, fun _ => rfl, Filter.Eventually.of_forall (fun _ => rfl), ?_⟩
  intro hξ
  change A (ξ.value 0) = 0
  rw [hξ, map_zero]

/-- Appendix C.6 (`app:kv2d_linear_fit`): the coordinate change preserves
the characteristic polynomial and hence its real and complex roots. -/
theorem transformed_charpoly {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E)
    (D : BlockState n E →ₗ[ℝ] BlockState n E) :
    LinearMap.charpoly (S.symm.toLinearMap.comp (D.comp S.toLinearMap)) =
      LinearMap.charpoly D := by
  change (S.symm.conj D).charpoly = D.charpoly
  exact S.symm.charpoly_conj D

/-- Appendix C.6: fifteen scalar states correspond to five plane-strain
tensor blocks, each with three independent components. -/
theorem plane_state_dimension :
    KVApproximation.Tensor.strainDimension 2 = 3 ∧
      5 * KVApproximation.Tensor.strainDimension 2 = 15 := by
  norm_num [KVApproximation.Tensor.strainDimension]

end KVApproximation.Examples.LinearSurrogate
