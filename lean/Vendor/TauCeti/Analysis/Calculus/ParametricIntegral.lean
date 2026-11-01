/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Topology.Compactness.Normed

/-!
# Compact-parameter integration

Differentiation and continuous differentiability under an integral over the
compact unit interval, with independent domain and codomain universes.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff Interval

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiation under an integral over the compact unit interval for a continuously
differentiable parameterized function. -/
theorem hasFDerivAt_integral_Icc_of_contDiff
     (h : E → ℝ → F) (hh : ContDiff ℝ 1 h.uncurry) (x₀ : E) :
    HasFDerivAt (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t)
      (∫ t in Set.Icc (0 : ℝ) 1,
        (fderiv ℝ h.uncurry (x₀, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x₀ := by
  let h' : E → ℝ → E →L[ℝ] F := fun x t ↦
    (fderiv ℝ h.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hh' : Continuous h'.uncurry := by
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_eventually_norm_le
    (F := h'.uncurry) (x₀ := x₀) isOpen_univ (fun _ _ ↦ hh'.continuousAt)
    (fun _ _ ↦ Set.mem_univ _)
  simp only [Set.mem_univ, true_and] at hC
  let s : Set E := {x | ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖h' x t‖ ≤ C}
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (F := h) (F' := h')
    (bound := fun _ ↦ C) (s := s)
  · exact hC
  · exact Filter.Eventually.of_forall fun x ↦
      (hh.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hh.continuous.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  · exact (hh'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro x hx
    exact hx t ht
  · exact continuous_const.integrableOn_Icc
  · filter_upwards with t
    intro x _hx
    have hd := hh.differentiable_one.differentiableAt.hasFDerivAt.comp x
        (hasFDerivAt_id x |>.prodMk (hasFDerivAt_const t x))
    -- Expose the derivative of the fixed-`t` slice; `inl` is definitionally `id.prod 0`.
    change HasFDerivAt (fun y ↦ h y t)
      ((fderiv ℝ h.uncurry (x, t)).comp ((ContinuousLinearMap.id ℝ E).prod 0)) x at hd
    simpa only [h', ContinuousLinearMap.inl] using hd

private theorem contDiff_integral_Icc_of_contDiff_nat
    {V : Type u} {W : Type max u v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (n : ℕ) (h : V → ℝ → W) (hh : ContDiff ℝ n h.uncurry) :
    ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  induction n generalizing W with
  | zero =>
      have hc : Continuous (fun x ↦ ∫ t in (0 : ℝ)..1, h x t) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          hh.continuous 0 1
      apply contDiff_zero.2
      simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
        using hc
  | succ n ih =>
      let h' : V → ℝ → V →L[ℝ] W := fun x t ↦
        (fderiv ℝ h.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ V ℝ)
      have hh' : ContDiff ℝ n h'.uncurry := by
        fun_prop
      have hsmooth : ContDiff ℝ ((n : ℕ∞ω) + 1)
          (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
        rw [contDiff_succ_iff_hasFDerivAt]
        exact ⟨fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h' x t, ih h' hh',
          hasFDerivAt_integral_Icc_of_contDiff h (hh.of_le (by norm_num))⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hsmooth

/-- Integration over the compact unit interval preserves continuous differentiability of any
possibly infinite order in a parameter. -/
theorem contDiff_integral_Icc_of_contDiff
    {V : Type u} {W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (n : ℕ∞) (h : V → ℝ → W) (hh : ContDiff ℝ n h.uncurry) :
    ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, h x t) := by
  let eW : Type max u v := ULift.{u} W
  let isoW : eW ≃L[ℝ] W := ContinuousLinearEquiv.ulift
  let eh : V → ℝ → eW := fun x t ↦ isoW.symm (h x t)
  have heh : ContDiff ℝ n eh.uncurry := by
    apply isoW.symm.contDiff.comp hh
  have he : ContDiff ℝ n (fun x ↦ ∫ t in Set.Icc (0 : ℝ) 1, eh x t) := by
    rw [contDiff_iff_forall_nat_le]
    intro m hm
    exact contDiff_integral_Icc_of_contDiff_nat m eh (heh.of_le (by exact_mod_cast hm))
  convert isoW.contDiff.comp he using 1
  funext x
  simpa only [Function.comp_apply, eh, ContinuousLinearEquiv.apply_symm_apply] using
    (isoW.integral_comp_comm (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (fun t ↦ eh x t))
