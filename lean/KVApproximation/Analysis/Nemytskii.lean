module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Lipschitz composition on Lp
-/

public section

noncomputable section

open MeasureTheory

namespace KVApproximation.Analysis

/-- Example 2.1 and Remark 4.3, activation ingredient: a globally Lipschitz
map acts on Lp over a finite measure space with the same Lipschitz constant.
The map need not fix zero. -/
theorem exists_lipschitz_compositionLp
    {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ENNReal) [Fact (1 ≤ p)]
    {g : E → F} {K : NNReal} (hg : LipschitzWith K g) :
    ∃ G : Lp E p μ → Lp F p μ, LipschitzWith K G ∧
      ∀ f : Lp E p μ, (G f : X → F) =ᵐ[μ] fun x => g (f x) := by
  have hc : LipschitzWith K (fun x => g x - g 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hg.dist_le_mul x y
  have hc0 : g 0 - g 0 = 0 := sub_self _
  have hconst : MemLp (fun _ : X => g 0) p μ := memLp_const _
  let c : Lp F p μ := hconst.toLp (fun _ : X => g 0)
  refine ⟨fun f => hc.compLp hc0 f + c, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro f h
    simpa only [dist_add_right] using
      (hc.lipschitzWith_compLp (p := p) (μ := μ) hc0).dist_le_mul f h
  · intro f
    filter_upwards [Lp.coeFn_add (hc.compLp hc0 f) c,
      hc.coeFn_compLp hc0 f, hconst.coeFn_toLp] with x hsum hcenter hconstant
    rw [hsum, Pi.add_apply, hcenter, hconstant]
    exact sub_add_cancel _ _

end KVApproximation.Analysis
