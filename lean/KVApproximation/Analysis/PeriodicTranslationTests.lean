module

public import KVApproximation.Analysis.PeriodicVariationStability
public import TauCeti.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Divergence tests for periodic translations

Averaging a test along a segment gives a vector field whose divergence is
the difference of its endpoint translates. The fibre retains its Euclidean norm.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Lemma B.2, translation estimate: a difference of periodic tests is a
periodic divergence, with the exact Euclidean displacement bound. -/
theorem exists_periodic_divergence_eq_translate_sub (g : PeriodicC1 d F)
    (hg : ∀ y, ‖g.value y‖ ≤ 1) (v : EuclideanSpace ℝ (Fin d)) :
    ∃ ψ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F)),
      (∀ y, ‖ψ.value y‖ ≤ ‖v‖) ∧
      ∀ y, ψ.divergence y = g.value (y - toCell v) - g.value y := by
  let Φ : PeriodicCell d → F := fun y =>
    ∫ t in (0 : ℝ)..1, g.value (y - toCell (t • v))
  have hlift (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
      toCell x - toCell (t • v) = toCell (x - t • v) := by
    ext i
    exact (AddCircle.coe_sub 1 _ _).symm
  have hΦ : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin d) => Φ (toCell x)) := by
    have hc := contDiff_integral_Icc_of_contDiff (1 : ℕ∞)
      (fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) => g.value (toCell (x - t • v)))
      (g.contDiff_lift.comp (contDiff_fst.sub (contDiff_snd.smul contDiff_const)))
    simpa [Φ, hlift, intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc] using hc
  let L : F →L[ℝ] PiLp 2 (fun _ : Fin d => F) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => F)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => (-v i) • ContinuousLinearMap.id ℝ F)
  have hL (z : F) (i : Fin d) : L z i = (-v i) • z := rfl
  let ψ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F)) :=
    ⟨fun y => L (Φ y), L.contDiff.comp hΦ⟩
  refine ⟨ψ, fun y => ?_, fun y => ?_⟩
  · have havg : ‖Φ y‖ ≤ 1 := by
      simpa only [sub_zero, abs_one, one_mul] using
        intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun t => g.value (y - toCell (t • v)))
          (a := 0) (b := 1) (C := 1) (fun t _ => hg _)
    have hnorm : ‖L (Φ y)‖ = ‖v‖ * ‖Φ y‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
      simp only [PiLp.norm_sq_eq_of_L2, hL, norm_smul, Real.norm_eq_abs, abs_neg,
        mul_pow, sq_abs, ← Finset.sum_mul]
    change ‖L (Φ y)‖ ≤ ‖v‖
    rw [hnorm]
    exact mul_le_of_le_one_right (norm_nonneg _) havg
  · let x := cellRepresentative y
    have hxy : toCell x = y := toCell_cellRepresentative y
    let U : EuclideanSpace ℝ (Fin d) → F := fun z => Φ (toCell z)
    have hUd := hΦ.differentiable_one x
    have hderiv := (L.hasFDerivAt.comp x hUd.hasFDerivAt).fderiv
    change fderiv ℝ (fun z => L (U z)) x = L.comp (fderiv ℝ U x) at hderiv
    have hdiv : ψ.divergence y = fderiv ℝ U x (-v) := by
      change (∑ i : Fin d,
        (fderiv ℝ (fun z => L (U z)) x (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) i) = _
      rw [hderiv]
      simp only [ContinuousLinearMap.comp_apply, hL]
      have hb := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (-v)
      have hmap := congrArg (fderiv ℝ U x) hb
      simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
        EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.single, PiLp.neg_apply] using hmap
    let f : ℝ → F := fun t => g.value (toCell (x - t • v))
    have hf : Continuous f := g.contDiff_lift.continuous.comp (by fun_prop)
    have hline : (fun s : ℝ => U (x + s • -v)) =
        fun s => (∫ t in (0 : ℝ)..s + 1, f t) - ∫ t in (0 : ℝ)..s, f t := by
      funext s
      rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _)]
      have hshift := intervalIntegral.integral_comp_add_right f s (a := 0) (b := 1)
      rw [zero_add, add_comm 1 s] at hshift
      rw [← hshift]
      change (∫ t in (0 : ℝ)..1, g.value (toCell (x + s • -v) - toCell (t • v))) = _
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hlift]
      simp only [f, smul_neg, add_smul]
      congr 2
      abel
    have hlineDeriv : HasLineDerivAt ℝ U (f 1 - f 0) x (-v) := by
      unfold HasLineDerivAt
      rw [hline]
      have h1 := (hf.integral_hasStrictDerivAt 0 (0 + 1)).hasDerivAt.comp_add_const 0 1
      exact (h1.sub (hf.integral_hasStrictDerivAt 0 0).hasDerivAt).congr_deriv (by simp)
    rw [hdiv, ← hUd.lineDeriv_eq_fderiv, hlineDeriv.lineDeriv]
    have hzero : toCell (0 : EuclideanSpace ℝ (Fin d)) = 0 := by ext i; rfl
    simp only [f, one_smul, zero_smul, ← hlift, hxy, hzero, sub_zero]

end KVApproximation.Analysis
