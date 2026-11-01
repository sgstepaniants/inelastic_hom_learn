module

public import KVApproximation.Examples.LinearSurrogate
public import KVApproximation.Tensor.Spaces
public import KVApproximation.Tensor.MandelFiniteIsometry
public import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Changes of coordinates for fitted linear responses
-/

public section

open KVApproximation.Dynamics

namespace KVApproximation.Examples.LinearSurrogate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Appendix C.6 (`app:kv2d_linear_fit`): a full-row-rank stress map can be
reduced to a sum of tensor blocks by an invertible state-coordinate change.
The fitted affine offsets have already been subtracted. -/
theorem exists_sum_coordinates {n : ℕ} (hn : 0 < n)
    (B : BlockState n E →ₗ[ℝ] E) (hB : Function.Surjective B) :
    ∃ S : BlockState n E ≃ₗ[ℝ] BlockState n E,
      ∀ q : BlockState n E, B (S q) = ∑ i : Fin n, q i := by
  sorry

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
  sorry

/-- Appendix C.6 (`app:kv2d_linear_fit`): transforming the state transports
the input and evolution maps to `S⁻¹ C` and `S⁻¹ D S`. These fitted maps are
arbitrary linear maps; no symmetry or dissipativity is asserted. -/
theorem transformed_kinetics {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E)
    (C : E →ₗ[ℝ] BlockState n E) (D : BlockState n E →ₗ[ℝ] BlockState n E)
    (v : E) (q : BlockState n E) :
    S.symm (C v + D (S q)) = (S.symm.toLinearMap.comp C) v +
      (S.symm.toLinearMap.comp (D.comp S.toLinearMap)) q := by
  sorry

/-- Appendix C.6 and Section 5.1 (`eqns:learned_fitted_dynamics`): the
transformed kinetic equation is the stated sum of input and evolution blocks. -/
theorem transformed_kinetic_blocks {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E)
    (C : E →ₗ[ℝ] BlockState n E) (D : BlockState n E →ₗ[ℝ] BlockState n E)
    (v : E) (q : BlockState n E) (i : Fin n) :
    (S.symm (C v + D (S q))) i = inputBlock S C i v +
      ∑ j : Fin n, evolutionBlock S D i j (q j) := by
  sorry

/-- Appendix C.6 and Section 5.1: the full stress formula retains both
instantaneous terms and replaces the state term by the sum of tensor blocks. -/
theorem transformed_stress {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E) (B : BlockState n E →ₗ[ℝ] E)
    (hBS : ∀ q : BlockState n E, B (S q) = ∑ i : Fin n, q i)
    (Av Ae : E →ₗ[ℝ] E) (v e : E) (q : BlockState n E) :
    Av v + Ae e + B (S q) = Av v + Ae e + ∑ i : Fin n, q i := by
  sorry

/-- Appendix C.6: the constant invertible coordinate change transports
bounded Sobolev trajectories and their velocities, including the initial state. -/
theorem trajectory_coordinates [CompleteSpace E] {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E) (ξ : BoundedTrajectory (BlockState n E)) :
    ∃ q : BoundedTrajectory (BlockState n E),
      (∀ t : ℝ, q.value t = S.symm (ξ.value t)) ∧
      (q.velocity =ᵐ[timeMeasure] fun t => S.symm (ξ.velocity t)) ∧
      (ξ.value 0 = 0 → q.value 0 = 0) := by
  sorry

/-- Appendix C.6 (`app:kv2d_linear_fit`): the coordinate change preserves
the characteristic polynomial and hence its real and complex roots. -/
theorem transformed_charpoly {n : ℕ}
    (S : BlockState n E ≃ₗ[ℝ] BlockState n E)
    (D : BlockState n E →ₗ[ℝ] BlockState n E) :
    LinearMap.charpoly (S.symm.toLinearMap.comp (D.comp S.toLinearMap)) =
      LinearMap.charpoly D := by
  sorry

/-- Appendix C.6: fifteen scalar states correspond to five plane-strain
tensor blocks, each with three independent components. -/
theorem plane_state_dimension :
    KVApproximation.Tensor.strainDimension 2 = 3 ∧
      5 * KVApproximation.Tensor.strainDimension 2 = 15 := by
  sorry

end KVApproximation.Examples.LinearSurrogate
