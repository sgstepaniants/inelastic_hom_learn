module

public import KVApproximation.Tensor.MultiplicationIdentities
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Pointwise and integrated coefficient bounds

The coefficient hypotheses in Proposition 3.3 can be tested on localized
constant strains. A countable dense set then gives a single exceptional null
set for all strains.
-/

public section

open MeasureTheory
open scoped InnerProductSpace ENNReal
open KVApproximation.Analysis

namespace KVApproximation.Tensor

private theorem integrable_fixed_energy {d : ℕ} (A : CoefficientField d ⊤)
    (v : Symmetric d) :
    Integrable (fun y => ⟪v, action (A y) v⟫_ℝ) (cellMeasure d) := by
  exact ((innerSL ℝ v).comp ((actionL d).flip v)).integrable_comp
    ((Lp.memLp A).integrable (by simp))

private theorem localized_energy {d : ℕ} (A : CoefficientField d ⊤)
    {s : Set (PeriodicCell d)} (hs : MeasurableSet s)
    (hμs : cellMeasure d s ≠ ∞) (v : Symmetric d) :
    fieldPairing A (indicatorConstLp 2 hs hμs v) (indicatorConstLp 2 hs hμs v) =
      ∫ y in s, ⟪v, action (A y) v⟫_ℝ ∂cellMeasure d := by
  rw [fieldPairing, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := v)] with y hy
  by_cases hys : y ∈ s
  · simp [hy, hys]
  · simp [hy, hys]

private theorem localized_norm_sq {d : ℕ} {s : Set (PeriodicCell d)}
    (hs : MeasurableSet s) (hμs : cellMeasure d s ≠ ∞) (v : Symmetric d) :
    ‖indicatorConstLp 2 hs hμs v‖ ^ 2 =
      ∫ _ in s, ‖v‖ ^ 2 ∂cellMeasure d := by
  rw [← real_inner_self_eq_norm_sq (indicatorConstLp 2 hs hμs v),
    L2.inner_indicatorConstLp_indicatorConstLp hs hs hμs hμs v v]
  simp

private theorem fixed_bounds_ae {d : ℕ} {α β : ℝ} (A : CoefficientField d ⊤)
    (hA : HasFieldBounds α β A) (v : Symmetric d) :
    ∀ᵐ y ∂cellMeasure d,
      α * ‖v‖ ^ 2 ≤ ⟪v, action (A y) v⟫_ℝ ∧
        ⟪v, action (A y) v⟫_ℝ ≤ β * ‖v‖ ^ 2 := by
  have hlo : (fun _ => α * ‖v‖ ^ 2) ≤ᵐ[cellMeasure d]
      (fun y => ⟪v, action (A y) v⟫_ℝ) := by
    apply ae_le_of_forall_setIntegral_le (integrable_const _) (integrable_fixed_energy A v)
    intro s hs hμs
    have h := (hA (indicatorConstLp 2 hs hμs.ne v)).1
    rwa [localized_energy, localized_norm_sq, ← integral_const_mul] at h
  have hhi : (fun y => ⟪v, action (A y) v⟫_ℝ) ≤ᵐ[cellMeasure d]
      (fun _ => β * ‖v‖ ^ 2) := by
    apply ae_le_of_forall_setIntegral_le (integrable_fixed_energy A v) (integrable_const _)
    intro s hs hμs
    have h := (hA (indicatorConstLp 2 hs hμs.ne v)).2
    rwa [localized_energy, localized_norm_sq, ← integral_const_mul] at h
  exact hlo.and hhi

/-- Proposition 3.3, coefficient hypotheses: pointwise and integrated
quadratic-form bounds agree for essentially bounded tensor fields. -/
theorem hasFieldBounds_iff_ae {d : ℕ} {α β : ℝ}
    (A : CoefficientField d ⊤) :
    HasFieldBounds α β A ↔ ∀ᵐ y ∂cellMeasure d, HasBounds α β (A y) := by
  constructor
  · intro hA
    obtain ⟨S, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense (Symmetric d)
    have hS : ∀ᵐ y ∂cellMeasure d, ∀ v ∈ S,
        α * ‖v‖ ^ 2 ≤ ⟪v, action (A y) v⟫_ℝ ∧
          ⟪v, action (A y) v⟫_ℝ ≤ β * ‖v‖ ^ 2 :=
      (ae_ball_iff hcount).2 fun v _ => fixed_bounds_ae A hA v
    filter_upwards [hS] with y hy
    have hq : Continuous (fun v : Symmetric d => ⟪v, action (A y) v⟫_ℝ) :=
      continuous_id.inner (actionL d (A y)).continuous
    intro v
    exact ⟨le_on_closure (fun w hw => (hy w hw).1)
        (continuous_const.mul (continuous_norm.pow 2)).continuousOn hq.continuousOn (hdense v),
      le_on_closure (fun w hw => (hy w hw).2)
        hq.continuousOn (continuous_const.mul (continuous_norm.pow 2)).continuousOn (hdense v)⟩
  · intro hA e
    have hi : Integrable (fun y => ‖e y‖ ^ 2) (cellMeasure d) := by
      simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) e e
    have he : ∫ y, ‖e y‖ ^ 2 ∂cellMeasure d = ‖e‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq e, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    have hlo := integral_mono_ae (hi.const_mul α) (integrable_fieldPairing A e e)
      (hA.mono fun y hy => (hy (e y)).1)
    have hhi := integral_mono_ae (integrable_fieldPairing A e e) (hi.const_mul β)
      (hA.mono fun y hy => (hy (e y)).2)
    simpa only [integral_const_mul, he, fieldPairing] using And.intro hlo hhi

end KVApproximation.Tensor
