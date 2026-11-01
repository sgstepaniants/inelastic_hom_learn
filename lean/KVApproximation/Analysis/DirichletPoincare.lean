module

public import KVApproximation.Analysis.VectorSobolevProperties
public import KVApproximation.Analysis.ZeroBoundaryCoordinates
public import TauCeti.Analysis.Sobolev.Poincare.W1p0

/-!
# Poincaré estimates for zero-boundary displacements
-/

public section

open MeasureTheory TopologicalSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, spatial coercivity: a domain contained in a ball of
radius R has a vector Dirichlet Poincaré bound with constant 2R. -/
theorem ZeroBoundaryH1.poincare_of_subset_ball {c : PhysicalSpace d} {R : ℝ}
    (hR : 0 ≤ R) (hΩ : (Ω : Set (PhysicalSpace d)) ⊆ Metric.ball c R)
    (u : ZeroBoundaryH1 Ω) :
    ‖VectorH1.valueL Ω u.val‖ ≤ 2 * R * ‖VectorH1.gradientL Ω u.val‖ := by
  have hc (i : Fin d) : ‖TauCeti.W1p.value (u.val i)‖ ≤
      2 * R * ‖TauCeti.W1p.gradient (u.val i)‖ := by
    cases d with
    | zero => exact Fin.elim0 i
    | succ n =>
      exact TauCeti.W1p.norm_value_le_mul_norm_gradient_of_subset_ball
        (p := 2) (u := u.val i) hΩ ((mem_zeroBoundary_iff u.val).mp u.property i)
  have hs : (∑ i, ‖TauCeti.W1p.value (u.val i)‖ ^ 2) ≤
      (2 * R) ^ 2 * ∑ i, ‖TauCeti.W1p.gradient (u.val i)‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      ‖TauCeti.W1p.value (u.val i)‖ ^ 2 ≤
          (2 * R * ‖TauCeti.W1p.gradient (u.val i)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hc i) 2
      _ = (2 * R) ^ 2 * ‖TauCeti.W1p.gradient (u.val i)‖ ^ 2 := by ring
  rw [← VectorH1.norm_valueL_sq, ← VectorH1.norm_gradientL_sq] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
    (by nlinarith [hs])

/-- Theorem 3.1, spatial coercivity: boundedness of the domain gives one
positive Poincaré constant for all displacements and microscopic scales. -/
theorem ZeroBoundaryH1.exists_poincare_constant
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ZeroBoundaryH1 Ω,
      ‖VectorH1.valueL Ω u.val‖ ≤ C * ‖VectorH1.gradientL Ω u.val‖ := by
  obtain ⟨R, hR, hball⟩ := hΩ.subset_ball_lt 0 (0 : PhysicalSpace d)
  refine ⟨2 * R, by positivity, ?_⟩
  exact fun u => ZeroBoundaryH1.poincare_of_subset_ball hR.le hball u

end KVApproximation.Analysis
