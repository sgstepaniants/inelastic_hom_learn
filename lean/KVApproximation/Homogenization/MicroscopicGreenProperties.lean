module

public import KVApproximation.Homogenization.MicroscopicGreen
public import KVApproximation.Homogenization.MicroscopicTrajectoryProperties

/-!
# Uniform bounds for microscopic Green operators
-/

public section

noncomputable section

open TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1, uniform Duhamel bounds: pointwise bounds proportional
to the input norm give operator bounds and time Lipschitz continuity. -/
private theorem operator_family_bounds_of_apply
    {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : ℝ → F →L[ℝ] H) {C : ℝ} (hC : 0 ≤ C)
    (hvalue : ∀ g t, 0 ≤ t → ‖A t g‖ ≤ C * ‖g‖)
    (hlip : ∀ g, LipschitzOnWith (Real.toNNReal (C * ‖g‖))
      (fun t => A t g) (Set.Ici (0 : ℝ))) :
    (∀ t : ℝ, 0 ≤ t → ‖A t‖ ≤ C) ∧
      LipschitzOnWith (Real.toNNReal C) A (Set.Ici (0 : ℝ)) := by
  refine ⟨fun t ht => (A t).opNorm_le_bound hC (fun g => hvalue g t ht), ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm, Real.coe_toNNReal _ hC]
  apply (A s - A t).opNorm_le_bound (mul_nonneg hC dist_nonneg)
  intro g
  calc
    ‖(A s - A t) g‖ = dist (A s g) (A t g) := by
      rw [sub_apply, dist_eq_norm]
    _ ≤ ((Real.toNNReal (C * ‖g‖) : ℝ)) * dist s t :=
      (hlip g).dist_le_mul s hs t ht
    _ = (C * dist s t) * ‖g‖ := by
      rw [Real.coe_toNNReal _ (mul_nonneg hC (norm_nonneg g))]
      ring

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, viscous preparation in Duhamel's formula: applying the
Green operator is the homogeneous trajectory of the viscous elliptic load. -/
theorem microscopicGreen_apply (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (ε : ℝ) (hε : ε ≠ 0) (t : ℝ) (g : SpatialL2 Ω) :
    microscopicGreen (Ω := Ω) V E hΩ ε t g =
      microscopicTrajectory (Ω := Ω) V E hΩ ε hε
        (microscopicLoadL (Ω := Ω) V hΩ ε hε g) t := by
  simp only [microscopicGreen, dite_eq_left hε, ContinuousLinearMap.comp_apply,
    microscopicTrajectory]

/-- Theorem 3.1, domination of the forcing contribution: one positive
constant bounds every Green operator on the nonnegative half-line and
their time Lipschitz constants in operator norm, before the scale is chosen. -/
theorem exists_uniform_microscopicGreen_bounds (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ,
      (∀ t : ℝ, 0 ≤ t → ‖microscopicGreen (Ω := Ω) V E hΩ ε t‖ ≤ C) ∧
      LipschitzOnWith (Real.toNNReal C)
        (microscopicGreen (Ω := Ω) V E hΩ ε) (Set.Ici (0 : ℝ)) := by
  obtain ⟨B, hB, hoperators⟩ := exists_uniform_microscopic_operator_bounds (Ω := Ω) V E hΩ
  obtain ⟨M, hM, htrajectory⟩ := exists_uniform_microscopicTrajectory_bounds (Ω := Ω) V E hΩ
  refine ⟨M * B, mul_pos hM hB, ?_⟩
  intro ε
  by_cases hε : ε ≠ 0
  · refine operator_family_bounds_of_apply
      (microscopicGreen (Ω := Ω) V E hΩ ε) (C := M * B)
      (mul_nonneg hM.le hB.le) ?_ ?_
    · intro g t ht
      rw [microscopicGreen_apply V E hΩ ε hε]
      calc
        ‖microscopicTrajectory V E hΩ ε hε (microscopicLoadL V hΩ ε hε g) t‖ ≤
            M * ‖microscopicLoadL V hΩ ε hε g‖ :=
          (htrajectory ε hε _).1 t ht
        _ ≤ M * (B * ‖g‖) := mul_le_mul_of_nonneg_left
          ((hoperators ε hε).2 g) hM.le
        _ = (M * B) * ‖g‖ := by ring
    · intro g
      have hload : ‖microscopicLoadL V hΩ ε hε g‖ ≤ B * ‖g‖ :=
        (hoperators ε hε).2 g
      have hbound : M * ‖microscopicLoadL V hΩ ε hε g‖ ≤ (M * B) * ‖g‖ := by
        calc
          _ ≤ M * (B * ‖g‖) := mul_le_mul_of_nonneg_left hload hM.le
          _ = _ := by ring
      simpa only [microscopicGreen_apply V E hΩ ε hε] using
        ((htrajectory ε hε (microscopicLoadL V hΩ ε hε g)).2.weaken
          (Real.toNNReal_mono hbound))
  · constructor
    · intro t _
      simpa only [microscopicGreen, dite_eq_right hε, ContinuousLinearMap.opNorm_zero] using
        (mul_nonneg hM.le hB.le)
    · apply LipschitzOnWith.of_dist_le_mul
      intro s hs t ht
      simp only [microscopicGreen, dite_eq_right hε, dist_self]
      positivity

end KVApproximation.Homogenization
