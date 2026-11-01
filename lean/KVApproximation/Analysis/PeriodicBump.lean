module

public import KVApproximation.Analysis.PeriodicSmoothIdentities
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Smooth periodic fields supported in a coordinate strip
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace KVApproximation.Analysis

/-- Proposition 4.7 (`prop:no_spectral_stability`), localized strains:
a periodic partial derivative vanishes outside the topological support
of the displacement field. The derivative is taken on its Euclidean lift. -/
theorem PeriodicC1.partial_eq_zero_of_notMem_tsupport
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : PeriodicC1 d F) (j : Fin d) {y : PeriodicCell d}
    (hy : y ∉ tsupport φ.value) : φ.partial j y = 0 := by
  have hc : Continuous (toCell (d := d)) :=
    continuous_pi fun k => (AddCircle.continuous_mk' (1 : ℝ)).comp
      (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) k)
  have ht : Tendsto (toCell (d := d)) (𝓝 (cellRepresentative y)) (𝓝 y) := by
    simpa only [toCell_cellRepresentative] using hc.tendsto (cellRepresentative y)
  have hz : (fun x : EuclideanSpace ℝ (Fin d) => φ.value (toCell x)) =ᶠ[𝓝 (cellRepresentative y)]
      fun _ => (0 : F) := (notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto ht
  have hn : cellRepresentative y ∉ tsupport
      (fun x : EuclideanSpace ℝ (Fin d) => φ.value (toCell x)) :=
    notMem_tsupport_iff_eventuallyEq.mpr hz
  rw [PeriodicC1.partial, fderiv_of_notMem_tsupport ℝ hn, zero_apply]

/-- Proposition 4.7, localized bump: outside the strip, the centered
periodic cosine stays below its value at the two strip faces. -/
private theorem cos_phase_le_outside_strip {a r : ℝ}
    (ha : 0 ≤ a) (har : a ≤ r) (hr : r ≤ 1) :
    Real.cos (2 * Real.pi * (r - a / 2)) ≤ Real.cos (Real.pi * a) := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hlo : Real.pi * a ≤ 2 * Real.pi * (r - a / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left har (show 0 ≤ 2 * Real.pi by positivity)]
  have hhi : 2 * Real.pi * (r - a / 2) ≤ 2 * Real.pi - Real.pi * a := by
    nlinarith [mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * Real.pi by positivity)]
  by_cases hhalf : 2 * Real.pi * (r - a / 2) ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hpi ha) hhalf hlo
  · have hreflect : Real.cos (2 * Real.pi - 2 * Real.pi * (r - a / 2)) ≤
        Real.cos (Real.pi * a) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hpi ha) (by linarith) (by linarith)
    simpa only [Real.cos_two_pi_sub] using hreflect

/-- Proposition 4.7 (`prop:no_spectral_stability`), localized corrector:
every positive-width coordinate strip contains the support of a smooth
periodic scalar bump attaining one and taking values between zero and one. -/
theorem exists_periodic_strip_bump {d : ℕ} (i : Fin d)
    {a : ℝ} (ha : 0 < a) (ha_one : a ≤ 1) :
    ∃ φ : PeriodicC1 d ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => φ.value (toCell x)) ∧
      (∀ y, 0 ≤ φ.value y ∧ φ.value y ≤ 1) ∧
      tsupport φ.value ⊆
        {y : PeriodicCell d | 0 < cellRepresentative y i ∧ cellRepresentative y i < a} ∧
      ∃ y, φ.value y = 1 := by
  classical
  let δ : ℝ := (1 - Real.cos (Real.pi * a)) / 2
  have hcos : Real.cos (Real.pi * a) < 1 := by
    have hangle : Real.pi * a ≤ Real.pi := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ha_one Real.pi_pos.le
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) le_rfl hangle (mul_pos Real.pi_pos ha)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let b : ContDiffBump (1 : ℝ) :=
    ⟨δ / 2, δ, by positivity, by linarith⟩
  let k : ℝ → ℝ := fun r => Real.cos (2 * Real.pi * (r - a / 2))
  have hk : Function.Periodic k 1 := by
    intro r
    change Real.cos (2 * Real.pi * (r + 1 - a / 2)) = Real.cos (2 * Real.pi * (r - a / 2))
    have heq : 2 * Real.pi * (r + 1 - a / 2) = 2 * Real.pi * (r - a / 2) + 2 * Real.pi := by ring
    rw [heq, Real.cos_add_two_pi]
  let χvalue : PeriodicCell d → ℝ := fun y => hk.lift (y i)
  have hχ : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin d) => χvalue (toCell x)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.cos (2 * Real.pi * (x i - a / 2)))
    exact (contDiff_const.mul
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).contDiff.sub contDiff_const)).cos
  let χ : PeriodicC1 d ℝ := ⟨χvalue, hχ.of_le (by simp)⟩
  let φ : PeriodicC1 d ℝ :=
    ⟨fun y => b (χ.value y), b.contDiff.comp χ.contDiff_lift⟩
  have hφsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin d) => φ.value (toCell x)) := b.contDiff.comp hχ
  let S : Set (PeriodicCell d) := {y | 1 - δ ≤ χ.value y}
  have hSclosed : IsClosed S := isClosed_le continuous_const χ.continuous_value
  have hsupport : Function.support φ.value ⊆ S := by
    intro y hy
    have hb : χ.value y ∈ Function.support b := hy
    rw [b.support_eq, Metric.mem_ball] at hb
    have habs : |χ.value y - 1| < δ := by simpa only [Real.dist_eq] using hb
    change 1 - δ ≤ χ.value y
    linarith [(abs_lt.mp habs).1]
  have hSstrip : S ⊆
      {y : PeriodicCell d | 0 < cellRepresentative y i ∧ cellRepresentative y i < a} := by
    intro y hy
    have hr : cellRepresentative y i ∈ Set.Ioc (0 : ℝ) 1 := by
      change (AddCircle.equivIoc (1 : ℝ) 0 (y i)).val ∈ Set.Ioc (0 : ℝ) 1
      simpa only [zero_add] using (AddCircle.equivIoc (1 : ℝ) 0 (y i)).property
    change 1 - δ ≤ χ.value y at hy
    change 0 < cellRepresentative y i ∧ cellRepresentative y i < a
    refine ⟨hr.1, ?_⟩
    by_contra hnot
    have hbound := cos_phase_le_outside_strip ha.le (le_of_not_gt hnot) hr.2
    have hχrep : χ.value y = Real.cos (2 * Real.pi * (cellRepresentative y i - a / 2)) :=
      (congrArg χ.value (toCell_cellRepresentative y)).symm
    rw [← hχrep] at hbound
    dsimp [δ] at hy
    linarith
  refine ⟨φ, hφsmooth, fun y => ⟨b.nonneg, b.le_one⟩,
    (closure_minimal hsupport hSclosed).trans hSstrip, ?_⟩
  let x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single i (a / 2))
  refine ⟨toCell x, ?_⟩
  have hχcenter : χ.value (toCell x) = 1 := by
    change Real.cos (2 * Real.pi * ((Pi.single i (a / 2) : Fin d → ℝ) i - a / 2)) = 1
    simp only [Pi.single_eq_same, sub_self, mul_zero, Real.cos_zero]
  change b (χ.value (toCell x)) = 1
  rw [hχcenter]
  exact b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)

end KVApproximation.Analysis
