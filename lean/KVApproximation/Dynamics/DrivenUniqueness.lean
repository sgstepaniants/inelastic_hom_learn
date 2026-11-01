module

public import KVApproximation.Dynamics.Caratheodory
public import KVApproximation.Dynamics.DrivenField
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Uniqueness for locally Lipschitz measurable-input equations
-/

public section

open MeasureTheory Set Metric

namespace KVApproximation.Dynamics

/-- Proposition B.13, uniqueness for the original kinetic response:
local Lipschitz continuity and a bounded measurable input suffice for
uniqueness of continuous integral solutions on a finite interval. -/
theorem locally_lipschitz_driven_unique_Icc
    {V Q : Type*} [NormedAddCommGroup V] [ProperSpace V]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {G : V × Q → Q} (hG : LocallyLipschitz G)
    {v : ℝ → V} {a b R : ℝ}
    (hv : AEStronglyMeasurable v (volume.restrict (Icc a b)))
    (hR : ∀ᵐ s ∂volume.restrict (Icc a b), ‖v s‖ ≤ R)
    {x₀ : Q} {x₁ x₂ : ℝ → Q}
    (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = x₀ + ∫ s in a..t, G (v s, x₁ s))
    (h₂ : ∀ t ∈ Icc a b, x₂ t = x₀ + ∫ s in a..t, G (v s, x₂ s)) :
    EqOn x₁ x₂ (Icc a b) := by
  let A := x₁ '' Icc a b ∪ x₂ '' Icc a b
  let S := closedBall (0 : V) R ×ˢ A
  have hA : IsCompact A := (isCompact_Icc.image_of_continuousOn hx₁).union
    (isCompact_Icc.image_of_continuousOn hx₂)
  have hS : IsCompact S := (isCompact_closedBall (0 : V) R).prod hA
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS hG.locallyLipschitzOn
  obtain ⟨H, hH, hEq⟩ := hK.extend_finite_dimension
  have hLip (s : ℝ) : LipschitzWith (lipschitzExtensionConstant Q * K)
      (fun q => H (v s, q)) := by
    apply LipschitzWith.of_dist_le_mul
    intro q q'
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
      hH.dist_le_mul (v s, q) (v s, q')
  have hInt (x : ℝ → Q) (hx : ContinuousOn x (Icc a b)) :
      IntegrableOn (fun s => H (v s, x s)) (Icc a b) :=
    integrableOn_lipschitz_driven_field hH hv hR hx
  have htransfer (x : ℝ → Q) (hxA : ∀ t ∈ Icc a b, x t ∈ A)
      (hsol : ∀ t ∈ Icc a b, x t = x₀ + ∫ s in a..t, G (v s, x s)) :
      ∀ t ∈ Icc a b, x t = x₀ + ∫ s in a..t, H (v s, x s) := by
    intro t ht
    rw [hsol t ht]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hR] with s hs hst
    rw [uIoc_of_le ht.1] at hst
    have hsmem : s ∈ Icc a b := ⟨hst.1.le, hst.2.trans ht.2⟩
    apply hEq
    exact ⟨by simpa only [mem_closedBall_iff_norm, sub_zero] using hs hsmem, hxA s hsmem⟩
  exact integral_solution_unique_Icc (Filter.Eventually.of_forall hLip) hInt hx₁ hx₂
    (htransfer x₁ (fun t ht => Or.inl ⟨t, ht, rfl⟩) h₁)
    (htransfer x₂ (fun t ht => Or.inr ⟨t, ht, rfl⟩) h₂)

end KVApproximation.Dynamics
