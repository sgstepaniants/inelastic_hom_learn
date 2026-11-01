module

public import KVApproximation.Analysis.TimeSobolevCoordinates
public import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Norm estimates for finite-time H¹ trajectories
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.1, time-space bounds: the value coordinate has the prescribed representative. -/
theorem TimeH1.valueL2_apply {T : ℝ} (u : TimeH1 H T) (t : ℝ) :
    TimeH1.valueL2 u t = TimeH1.value u t := by
  exact congrArg (fun v : Lp H 2 (volume.restrict (Set.Ioo 0 T)) => v t)
    (TauCeti.EvolutionSpace.valueL_apply (ι := ContinuousLinearMap.id ℝ H) (a := 0) (b := T) u)

/-- Theorem 3.1, time-space bounds: the velocity coordinate has the prescribed
Hilbert-valued weak derivative almost everywhere. -/
theorem TimeH1.velocityL2_apply_ae {T : ℝ} (u : TimeH1 H T) :
    TimeH1.velocityL2 u =ᵐ[volume.restrict (Set.Ioo 0 T)] TimeH1.velocity u := by
  dsimp only [TimeH1.velocityL2, ContinuousLinearMap.comp_apply]
  rw [TauCeti.EvolutionSpace.timeDerivL_apply (ι := ContinuousLinearMap.id ℝ H) (a := 0) (b := T) u]
  exact ((InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLp
    (TauCeti.EvolutionSpace.timeDeriv u)

/-- Theorem 3.1, time-space bounds: the actual graph norm is the Euclidean
sum of the L² value and Hilbert-valued velocity norms. -/
theorem TimeH1.norm_sq_eq_value_velocity {T : ℝ} (u : TimeH1 H T) :
    ‖u‖ ^ 2 = ‖TimeH1.valueL2 u‖ ^ 2 + ‖TimeH1.velocityL2 u‖ ^ 2 := by
  have hv : ‖TimeH1.velocityL2 u‖ = ‖TauCeti.EvolutionSpace.timeDeriv u‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [TimeH1.velocityL2_apply_ae u] with t ht
    rw [ht]
    exact (InnerProductSpace.toDual ℝ H).symm.norm_map _
  have hvalue : TimeH1.valueL2 u = TauCeti.EvolutionSpace.value u :=
    TauCeti.EvolutionSpace.valueL_apply (ι := ContinuousLinearMap.id ℝ H) (a := 0) (b := T) u
  exact (TauCeti.EvolutionSpace.norm_sq_eq_norm_value_sq_add_norm_timeDeriv_sq
    (ι := ContinuousLinearMap.id ℝ H) (a := 0) (b := T) u).trans
      (congrArg₂ (fun x y : ℝ => x ^ 2 + y ^ 2) (congrArg norm hvalue).symm hv.symm)

/-- Theorem 3.1, time-space bounds: the elementary graph-norm estimate. -/
private theorem graph_norm_bound {a b c d e : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsq : a ^ 2 = b ^ 2 + c ^ 2) (hder : c ≤ d * b + 1 * e) :
    a ≤ (1 + d) * b + e := by
  have hsum : a ≤ b + c := by nlinarith [mul_nonneg hb hc]
  linarith

set_option maxHeartbeats 400000 in
/-- Theorem 3.1, time-space bounds: a bounded linear evolution controls
the full H¹ norm by the L² value and forcing norms. -/
theorem TimeH1.norm_le_of_ode {T : ℝ} (A : H →L[ℝ] H)
    (f : Lp H 2 (volume.restrict (Set.Ioo 0 T))) (u : TimeH1 H T)
    (hode : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      TimeH1.velocity u t = A (TimeH1.value u t) + f t) :
    ‖u‖ ≤ (1 + ‖A‖) * ‖TimeH1.valueL2 u‖ + ‖f‖ := by
  have hv : ‖TimeH1.velocityL2 u‖ ≤ ‖A‖ * ‖TimeH1.valueL2 u‖ + 1 * ‖f‖ := by
    apply TauCeti.Lp.norm_le_add_of_ae_norm_le (norm_nonneg A) zero_le_one
    filter_upwards [TimeH1.velocityL2_apply_ae u, hode] with t ht hode_t
    rw [ht, hode_t, TimeH1.valueL2_apply, one_mul]
    exact (norm_add_le _ _).trans (add_le_add (A.le_opNorm _) le_rfl)
  exact graph_norm_bound (norm_nonneg (TimeH1.valueL2 u))
    (norm_nonneg (TimeH1.velocityL2 u)) (TimeH1.norm_sq_eq_value_velocity u) hv

end KVApproximation.Analysis
