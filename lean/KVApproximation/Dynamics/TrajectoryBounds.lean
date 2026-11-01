module

public import KVApproximation.Dynamics.Trajectory
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Bounds for the continuous trajectory representative

The integral identity upgrades the essential velocity bound to a Lipschitz
estimate. Continuity then makes the essential value bound hold at every time.
-/

public section

open MeasureTheory

namespace KVApproximation.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Section 4.1 and Lemma B.7: the velocity is bounded almost everywhere
by its essential supremum on the nonnegative time axis. -/
theorem BoundedTrajectory.norm_velocity_ae_le (e : BoundedTrajectory E) :
    ∀ᵐ t ∂timeMeasure, ‖e.velocity t‖ ≤ e.velocityBound :=
  ae_le_lpNorm_exponent_top e.velocity_memLp

/-- Lemma B.7 and Appendix B.3: the velocity is integrable on every
finite interval whose endpoints are nonnegative. -/
theorem BoundedTrajectory.velocity_intervalIntegrable (e : BoundedTrajectory E)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable e.velocity volume a b := by
  let : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) :=
    ⟨by simp [Set.uIoc, Real.volume_Ioc]⟩
  rw [intervalIntegrable_iff]
  apply MemLp.integrable le_top
  exact MemLp.mono_measure
    (Measure.restrict_mono_set volume (fun x hx => (le_min ha hb).trans hx.1.le))
    e.velocity_memLp

/-- Section 4.1 and Lemma B.7: the integral representative has the sharp
Lipschitz bound furnished by its essentially bounded velocity. -/
theorem BoundedTrajectory.norm_value_sub_le (e : BoundedTrajectory E)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖e.value b - e.value a‖ ≤ e.velocityBound * |b - a| := by
  rw [e.integral_eq b hb, e.integral_eq a ha, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left
      (e.velocity_intervalIntegrable le_rfl hb) (e.velocity_intervalIntegrable le_rfl ha)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
  have hae := ae_imp_of_ae_restrict e.norm_velocity_ae_le
  filter_upwards [hae] with x hx hxab
  exact hx ((le_min ha hb).trans hxab.1.le)

/-- Section 4.1 and Lemma B.7: the integral representative is continuous
on the closed nonnegative time axis, including the initial time. -/
theorem BoundedTrajectory.continuousOn_value (e : BoundedTrajectory E) :
    ContinuousOn e.value (Set.Ici 0) := by
  have hbound : 0 ≤ e.velocityBound := ENNReal.toReal_nonneg
  have hLip : LipschitzOnWith (Real.toNNReal e.velocityBound) e.value (Set.Ici 0) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro a ha b hb
    simpa only [dist_eq_norm, Real.norm_eq_abs, Real.coe_toNNReal _ hbound] using
      e.norm_value_sub_le hb ha
  exact hLip.continuousOn

/-- Lemma B.7, integration-by-parts estimate: the value bound holds
pointwise for the integral representative, including time zero. -/
theorem BoundedTrajectory.norm_value_le (e : BoundedTrajectory E)
    {t : ℝ} (ht : 0 ≤ t) : ‖e.value t‖ ≤ e.valueBound := by
  have hae : ∀ᵐ s ∂timeMeasure, ‖e.value s‖ ≤ e.valueBound :=
    ae_le_lpNorm_exponent_top e.value_memLp
  have heq : (fun s => min ‖e.value s‖ e.valueBound) =ᵐ[timeMeasure]
      (fun s => ‖e.value s‖) := hae.mono fun _ h => min_eq_left h
  have hc := e.continuousOn_value.norm
  have hpoint := Measure.eqOn_of_ae_eq heq (hc.inf continuousOn_const) hc
    (by simp only [interior_Ici, closure_Ioi, Set.Subset.refl])
  exact min_eq_left_iff.mp (hpoint ht)

end KVApproximation.Dynamics
