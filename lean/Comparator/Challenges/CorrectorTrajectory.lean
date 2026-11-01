module

public import KVApproximation.Homogenization.CorrectorTrajectory

/-!
# Recovery of periodic displacement trajectories
-/

public section

open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Section 3.1 (`eq:strain_corrector`) and Appendix A.3: a periodic
H¹ displacement trajectory has a unique strain-corrector trajectory. -/
theorem displacement_strain_exists_unique {d : ℕ} {T : ℝ}
    (χ : TimeH1 (ZeroMeanPeriodicH1 d) T) :
    ∃! η : TimeH1 (correctorSubspace d) T, IsDisplacementStrain (d := d) (T := T) χ η := by
  sorry

/-- Section 3.1 (`eq:strain_corrector`) and Appendix A.3: every finite-time
H¹ strain-corrector trajectory comes from a unique zero-mean periodic
displacement trajectory, with the corresponding weak time derivative. -/
theorem strain_displacement_exists_unique {d : ℕ} {T : ℝ}
    (η : TimeH1 (correctorSubspace d) T) :
    ∃! χ : TimeH1 (ZeroMeanPeriodicH1 d) T, IsDisplacementStrain (d := d) (T := T) χ η := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- Appendix A.3, initial preparation in `eq:cell_weak`: the symmetric-gradient
identification holds at every closed-interval time, including time zero. -/
theorem displacement_strain_trace {d : ℕ} {T : ℝ} (hT : 0 < T)
    (χ : TimeH1 (ZeroMeanPeriodicH1 d) T)
    (η : TimeH1 (correctorSubspace d) T)
    (h : IsDisplacementStrain (d := d) (T := T) χ η) (t : Set.Icc (0 : ℝ) T) :
    (@TimeH1.trace (correctorSubspace d) inferInstance inferInstance
      inferInstance T hT η t).val =
      correctorGradientL d (@TimeH1.trace (ZeroMeanPeriodicH1 d) inferInstance inferInstance
        inferInstance T hT χ t) := by
  sorry

end KVApproximation.Homogenization
