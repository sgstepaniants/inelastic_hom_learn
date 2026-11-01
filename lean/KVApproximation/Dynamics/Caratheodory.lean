/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from TauCeti v4.35.0, Analysis/ODE/Caratheodory.lean, to nonlinear
fields with a uniform state Lipschitz bound.
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Measurable-time nonlinear integral equations

The Picard map acts on continuous curves on a compact interval. Its
iterates satisfy a factorial estimate, so an iterate is a contraction.
The integrand may be merely measurable in time.

The construction follows the affine argument in
https://github.com/TauCetiProject/TauCeti/blob/v4.35.0/TauCeti/Analysis/ODE/Caratheodory.lean.
-/

public section

open Function MeasureTheory Set intervalIntegral
open scoped Nat NNReal

namespace KVApproximation.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E} {a b : ℝ} {K : ℝ≥0} {x₀ : E}

namespace Caratheodory

omit [NormedSpace ℝ E] in
private theorem integrableOn_Icc (hab : a ≤ b)
    (hInt : ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b)) (y : C(Icc a b, E)) :
    IntegrableOn (fun s => f s (IccExtend hab y s)) (Icc a b) :=
  hInt _ y.continuous.Icc_extend'.continuousOn

private noncomputable def next (hab : a ≤ b)
    (hInt : ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b))
    (x₀ : E) (y : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := ODE.picard f a x₀ (IccExtend hab y) t
  continuous_toFun := by
    have hI : IntegrableOn (fun s => f s (IccExtend hab y s)) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact integrableOn_Icc hab hInt y
    have h := continuousOn_primitive_interval hI
    rw [uIcc_of_le hab] at h
    exact (continuousOn_const.add h).comp_continuous continuous_subtype_val Subtype.prop

private theorem next_apply (hab : a ≤ b)
    (hInt : ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b))
    (y : C(Icc a b, E)) (t : Icc a b) :
    next hab hInt x₀ y t = ODE.picard f a x₀ (IccExtend hab y) t := rfl

variable (hab : a ≤ b)
  (hLip : ∀ᵐ s ∂volume.restrict (Icc a b), LipschitzWith K (f s))
  (hInt : ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
    IntegrableOn (fun s => f s (x s)) (Icc a b))

include hab hLip hInt in
private theorem dist_iterate_next_apply_le (n : ℕ)
    (y z : C(Icc a b, E)) (t : Icc a b) :
    dist ((next hab hInt x₀)^[n] y t) ((next hab hInt x₀)^[n] z t) ≤
      ((K : ℝ) * (t - a)) ^ n / n ! * dist y z := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) t
  | succ n ih =>
    set Y := (next hab hInt x₀)^[n] y
    set Z := (next hab hInt x₀)^[n] z
    have hint : ∀ W : C(Icc a b, E), IntervalIntegrable
        (fun s => f s (IccExtend hab W s)) volume a t := fun W =>
      (intervalIntegrable_iff_integrableOn_Icc_of_le t.2.1).2
        ((integrableOn_Icc hab hInt W).mono_set (Icc_subset_Icc_right t.2.2))
    have hLae : ∀ᵐ s, s ∈ Icc a b → LipschitzWith K (f s) :=
      (ae_restrict_iff' measurableSet_Icc).mp hLip
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      ODE.picard_apply, ODE.picard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hint Y) (hint Z)]
    calc
      _ ≤ ∫ s in a..t, (K : ℝ) * (((K : ℝ) * (s - a)) ^ n / n ! * dist y z) := by
        refine norm_integral_le_of_norm_le t.2.1 ?_
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        filter_upwards [hLae] with s hs hst
        have hs' : s ∈ Icc a b := ⟨hst.1.le, hst.2.trans t.2.2⟩
        rw [IccExtend_of_mem hab _ hs', IccExtend_of_mem hab _ hs']
        calc
          _ ≤ (K : ℝ) * dist (Y ⟨s, hs'⟩) (Z ⟨s, hs'⟩) := by
            simpa only [dist_eq_norm] using (hs hs').dist_le_mul (Y ⟨s, hs'⟩) (Z ⟨s, hs'⟩)
          _ ≤ _ := mul_le_mul_of_nonneg_left (ih ⟨s, hs'⟩) K.coe_nonneg
      _ = ((K : ℝ) * (t - a)) ^ (n + 1) / (n + 1)! * dist y z := by
        have : ∫ s in a..t, (K : ℝ) * (((K : ℝ) * (s - a)) ^ n / n ! * dist y z) =
            (K : ℝ) ^ (n + 1) * dist y z / n ! * ∫ s in a..t, (s - a) ^ n := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          ext s
          rw [mul_pow, pow_succ]
          ring
        rw [this, intervalIntegral.integral_comp_sub_right (fun s => s ^ n), integral_pow,
          sub_self, zero_pow n.succ_ne_zero, sub_zero, Nat.factorial_succ, mul_pow]
        push_cast
        field_simp

include hab hLip hInt in
private theorem exists_contractingWith_iterate_next :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next hab hInt x₀)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * (b - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have h₀ : 0 ≤ ((K : ℝ) * (b - a)) ^ n / n ! := by
    have : 0 ≤ b - a := sub_nonneg.2 hab
    positivity
  refine ⟨n, (((K : ℝ) * (b - a)) ^ n / n !).toNNReal, Real.toNNReal_lt_one.2 hn,
    LipschitzWith.of_dist_le_mul fun y z => ?_⟩
  rw [Real.coe_toNNReal _ h₀, ContinuousMap.dist_le (by positivity)]
  intro t
  refine (dist_iterate_next_apply_le hab hLip hInt n y z t).trans ?_
  have h₁ : 0 ≤ (K : ℝ) * (t - a) := mul_nonneg K.coe_nonneg (sub_nonneg.2 t.2.1)
  have h₂ : (K : ℝ) * (t - a) ≤ (K : ℝ) * (b - a) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right t.2.2 a) K.coe_nonneg
  gcongr

include hab hInt in
private theorem isFixedPt_next {x : ℝ → E} (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = x₀ + ∫ s in a..t, f s (x s)) :
    IsFixedPt (next hab hInt x₀) ⟨(Icc a b).domRestrict x, hx.domRestrict⟩ := by
  ext t
  rw [next_apply, ContinuousMap.coe_mk, domRestrict_apply, h t t.2, ODE.picard_apply]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Icc a b := uIcc_subset_Icc ⟨le_rfl, hab⟩ t.2 hs
  simp [IccExtend_of_mem hab _ hs']

end Caratheodory

open Caratheodory

/-- Proposition B.13, Carathéodory existence ingredient: a uniformly
Lipschitz field with integrable evaluations along continuous curves has
an integral solution on every finite interval in a complete Banach space. -/
theorem exists_integral_solution_Icc [CompleteSpace E]
    (hLip : ∀ᵐ s ∂volume.restrict (Icc a b), LipschitzWith K (f s))
    (hInt : ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b)) (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Icc a b) ∧ x a = x₀ ∧
      ∀ t ∈ Icc a b, x t = x₀ + ∫ s in a..t, f s (x s) := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨fun _ => x₀, continuousOn_const, rfl, by simp [Icc_eq_empty_of_lt hba]⟩
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) hab hLip hInt
  obtain ⟨y, hy⟩ : ∃ y, IsFixedPt (next hab hInt x₀) y :=
    ⟨_, hC.isFixedPt_fixedPoint_iterate⟩
  have hsol : ∀ t ∈ Icc a b,
      IccExtend hab y t = x₀ + ∫ s in a..t, f s (IccExtend hab y s) := by
    intro t ht
    rw [IccExtend_of_mem hab _ ht]
    conv_lhs => rw [← hy]
    rw [next_apply, ODE.picard_apply]
  exact ⟨IccExtend hab y, y.continuous.Icc_extend'.continuousOn,
    by simpa using hsol a (left_mem_Icc.2 hab), hsol⟩

/-- Proposition B.13, Carathéodory uniqueness ingredient: two continuous
integral solutions with the same initial value agree on the interval.
Completeness is needed for existence, but not for uniqueness. -/
theorem integral_solution_unique_Icc
    (hLip : ∀ᵐ s ∂volume.restrict (Icc a b), LipschitzWith K (f s))
    (hInt : ∀ x : ℝ → E, ContinuousOn x (Icc a b) →
      IntegrableOn (fun s => f s (x s)) (Icc a b))
    {x₁ x₂ : ℝ → E}
    (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = x₀ + ∫ s in a..t, f s (x₁ s))
    (h₂ : ∀ t ∈ Icc a b, x₂ t = x₀ + ∫ s in a..t, f s (x₂ s)) :
    EqOn x₁ x₂ (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · simp [Icc_eq_empty_of_lt hba]
  obtain ⟨n, C, hC⟩ := exists_contractingWith_iterate_next (x₀ := x₀) hab hLip hInt
  have := hC.fixedPoint_unique' ((isFixedPt_next hab hInt hx₁ h₁).iterate n)
    ((isFixedPt_next hab hInt hx₂ h₂).iterate n)
  exact fun t ht => congr($this ⟨t, ht⟩)

end KVApproximation.Dynamics
