module

public import KVApproximation.NeuralOperators.FourierMapping
public import KVApproximation.Analysis.Nemytskii
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Nonlinear lifting into periodic L²
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remark 4.3: a globally Lipschitz pointwise lifting
defines a globally Lipschitz map into L² for all vector and L² field inputs.
The global hypothesis supplies the required growth control. -/
theorem exists_lipschitz_channel_lifting {d vectorInput functionInput width : ℕ}
    {S : WithLp 2 (Channels vectorInput × Channels functionInput) → Channels width}
    {K : NNReal} (hS : LipschitzWith K S) :
    ∃ L : NNReal, ∃ A : Channels vectorInput × ChannelField d functionInput → ChannelField d width,
      LipschitzWith L A ∧ ∀ x : Channels vectorInput × ChannelField d functionInput,
        (A x : PeriodicCell d → Channels width) =ᵐ[cellMeasure d]
          fun y => S (WithLp.toLp 2 (x.1, x.2 y)) := by
  let U := WithLp 2 (Channels vectorInput × Channels functionInput)
  let J : (Channels vectorInput × Channels functionInput) →L[ℝ] U :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Channels vectorInput)
      (Channels functionInput)).symm.toContinuousLinearMap
  let V : Channels vectorInput →L[ℝ] U :=
    J.comp (ContinuousLinearMap.inl ℝ (Channels vectorInput) (Channels functionInput))
  let H : Channels functionInput →L[ℝ] U :=
    J.comp (ContinuousLinearMap.inr ℝ (Channels vectorInput) (Channels functionInput))
  let A : (Channels vectorInput × ChannelField d functionInput) →L[ℝ]
      Lp U 2 (cellMeasure d) :=
    ((Lp.constL 2 (cellMeasure d) ℝ).comp V).coprod (H.compLpL 2 (cellMeasure d))
  have hA (x : Channels vectorInput × ChannelField d functionInput) :
      (A x : PeriodicCell d → U) =ᵐ[cellMeasure d]
        fun y => WithLp.toLp 2 (x.1, x.2 y) := by
    change ((Lp.const 2 (cellMeasure d) (V x.1) + H.compLpL 2 (cellMeasure d) x.2 :
      Lp U 2 (cellMeasure d)) : PeriodicCell d → U) =ᵐ[cellMeasure d] _
    filter_upwards [Lp.coeFn_add (Lp.const 2 (cellMeasure d) (V x.1))
        (H.compLpL 2 (cellMeasure d) x.2),
      Lp.coeFn_const (p := 2) (μ := cellMeasure d) (c := V x.1),
      H.coeFn_compLpL x.2] with y hadd hconstant hfield
    rw [hadd, Pi.add_apply, hconstant, hfield]
    change J (x.1, 0) + J (0, x.2 y) = J (x.1, x.2 y)
    simpa using (J.map_add (x.1, 0) (0, x.2 y)).symm
  obtain ⟨N, hN, hNrep⟩ := exists_lipschitz_compositionLp (cellMeasure d) 2 hS
  refine ⟨K * ‖A‖₊, N ∘ A, hN.comp A.lipschitzWith, ?_⟩
  intro x
  filter_upwards [hNrep (A x), hA x] with y hNy hAy
  exact hNy.trans (congrArg S hAy)

end KVApproximation.NeuralOperators
