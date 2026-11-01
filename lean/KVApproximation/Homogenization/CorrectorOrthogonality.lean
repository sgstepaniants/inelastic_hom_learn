module

public import KVApproximation.Homogenization.CorrectorSpace
public import KVApproximation.Analysis.PeriodicGradientMean

/-!
# Orthogonality of constant strains and periodic correctors
-/

public section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Tensor
open scoped InnerProductSpace

namespace KVApproximation.Homogenization

/-- Appendix A.1: periodic corrector strains are orthogonal to every
constant macroscopic strain in the unweighted Frobenius L² inner product. -/
theorem constantStrain_orthogonal_corrector {d : ℕ} (e : Symmetric d)
    (η : correctorSubspace d) :
    ⟪constantStrainL d e, (η : StrainField d)⟫_ℝ = 0 := by
  let K : ClosedSubmodule ℝ (StrainField d) :=
    (⊥ : ClosedSubmodule ℝ ℝ).comap (innerSL ℝ (constantStrainL d e))
  have hle : correctorSubspace d ≤ K := by
    apply Submodule.closure_le.mpr
    rintro _ ⟨u, rfl⟩
    change ⟪constantStrainL d e, correctorGradientL d u⟫_ℝ = 0
    have hint : (∫ y, correctorGradientL d u y ∂cellMeasure d) = 0 := by
      calc
        (∫ y, correctorGradientL d u y ∂cellMeasure d) =
            ∫ y, symmetrizeL d (PeriodicH1.gradientL d u.val y) ∂cellMeasure d := by
          apply integral_congr_ae
          exact (symmetrizeL d).coeFn_compLpL (PeriodicH1.gradientL d u.val)
        _ = symmetrizeL d (∫ y, PeriodicH1.gradientL d u.val y ∂cellMeasure d) :=
          (symmetrizeL d).integral_comp_comm
            (MemLp.integrable (by norm_num) (Lp.memLp (PeriodicH1.gradientL d u.val)))
        _ = 0 := by rw [PeriodicH1.integral_gradient_eq_zero, map_zero]
    rw [L2.inner_def]
    have hconst : (∫ y, ⟪constantStrainL d e y, correctorGradientL d u y⟫_ℝ
        ∂cellMeasure d) = ∫ y, ⟪e, correctorGradientL d u y⟫_ℝ ∂cellMeasure d := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 (cellMeasure d) e] with y hy
      change ⟪(Lp.const 2 (cellMeasure d) e) y, correctorGradientL d u y⟫_ℝ = _
      rw [hy, Function.const_apply]
    rw [hconst, integral_inner
      (MemLp.integrable (by norm_num) (Lp.memLp (correctorGradientL d u))) e,
      hint, inner_zero_right]
  exact hle η.property

end KVApproximation.Homogenization
