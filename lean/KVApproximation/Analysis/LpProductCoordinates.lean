module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Combining two L² fields
-/

public section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Lemma B.12, material-coordinate step: two L² fields are continuously
equivalent to a single field with a Euclidean product value space. The
ordinary product of L² spaces carries its usual maximum norm. -/
theorem lp_product_coordinates {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure Ω) :
    ∃ U : (Lp E 2 μ × Lp F 2 μ) ≃L[ℝ] Lp (WithLp 2 (E × F)) 2 μ,
      ∀ f : Lp E 2 μ × Lp F 2 μ,
        ∀ᵐ y ∂μ, U f y = WithLp.toLp 2 (f.1 y, f.2 y) := by
  let I := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap
  let I₁ := I.comp (ContinuousLinearMap.inl ℝ E F)
  let I₂ := I.comp (ContinuousLinearMap.inr ℝ E F)
  let A := (I₁.compLpL 2 μ).coprod (I₂.compLpL 2 μ)
  let B₁ := WithLp.fstL 2 ℝ E F
  let B₂ := WithLp.sndL 2 ℝ E F
  let B := (B₁.compLpL 2 μ).prod (B₂.compLpL 2 μ)
  have hA (f : Lp E 2 μ × Lp F 2 μ) :
      ∀ᵐ y ∂μ, A f y = WithLp.toLp 2 (f.1 y, f.2 y) := by
    filter_upwards [Lp.coeFn_add (I₁.compLp f.1) (I₂.compLp f.2),
      I₁.coeFn_compLp f.1, I₂.coeFn_compLp f.2] with y hadd h₁ h₂
    change (I₁.compLp f.1 + I₂.compLp f.2) y = _
    rw [hadd, Pi.add_apply, h₁, h₂]
    change I (f.1 y, 0) + I (0, f.2 y) = I (f.1 y, f.2 y)
    rw [← map_add]
    simp
  have hB (f : Lp (WithLp 2 (E × F)) 2 μ) :
      ∀ᵐ y ∂μ, ((B f).1 y, (B f).2 y) = WithLp.ofLp (f y) := by
    filter_upwards [B₁.coeFn_compLp f, B₂.coeFn_compLp f] with y h₁ h₂
    change (B₁.compLp f y, B₂.compLp f y) = _
    rw [h₁, h₂]
    rfl
  have hBA (f : Lp E 2 μ × Lp F 2 μ) : B (A f) = f := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [hB (A f), hA f] with y hB' hA'
      rw [hA'] at hB'
      exact congrArg Prod.fst hB'
    · apply Lp.ext
      filter_upwards [hB (A f), hA f] with y hB' hA'
      rw [hA'] at hB'
      exact congrArg Prod.snd hB'
  have hAB (f : Lp (WithLp 2 (E × F)) 2 μ) : A (B f) = f := by
    apply Lp.ext
    filter_upwards [hA (B f), hB f] with y hA' hB'
    rw [hA', hB']
  let U : (Lp E 2 μ × Lp F 2 μ) ≃L[ℝ] Lp (WithLp 2 (E × F)) 2 μ :=
    { toLinearEquiv := { A.toLinearMap with invFun := B, left_inv := hBA, right_inv := hAB }
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  exact ⟨U, hA⟩

end KVApproximation.Analysis
