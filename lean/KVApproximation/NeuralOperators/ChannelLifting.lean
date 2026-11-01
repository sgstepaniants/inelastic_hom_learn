module

public import KVApproximation.NeuralOperators.FourierMapping
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Linear lifting of vector and field inputs
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1 and Remark 4.3, linear lifting: a pointwise linear map of
the vector and field channels induces a continuous linear map into L². -/
theorem exists_channel_liftingCLM {d vectorInput functionInput width : ℕ}
    (S : WithLp 2 (Channels vectorInput × Channels functionInput) →ₗ[ℝ] Channels width) :
    ∃ A : (Channels vectorInput × ChannelField d functionInput) →L[ℝ]
        ChannelField d width,
      ∀ x : Channels vectorInput × ChannelField d functionInput,
        (A x : PeriodicCell d → Channels width) =ᵐ[cellMeasure d]
          fun y => S (WithLp.toLp 2 (x.1, x.2 y)) := by
  let L : (Channels vectorInput × Channels functionInput) →L[ℝ] Channels width :=
    (S.comp
      (WithLp.linearEquiv 2 ℝ (Channels vectorInput × Channels functionInput)).symm.toLinearMap
      ).toContinuousLinearMap
  let V : Channels vectorInput →L[ℝ] Channels width :=
    L.comp (ContinuousLinearMap.inl ℝ (Channels vectorInput) (Channels functionInput))
  let H : Channels functionInput →L[ℝ] Channels width :=
    L.comp (ContinuousLinearMap.inr ℝ (Channels vectorInput) (Channels functionInput))
  let A : (Channels vectorInput × ChannelField d functionInput) →L[ℝ]
      ChannelField d width :=
    ((Lp.constL 2 (cellMeasure d) ℝ).comp V).coprod (H.compLpL 2 (cellMeasure d))
  refine ⟨A, ?_⟩
  intro x
  change ((Lp.const 2 (cellMeasure d) (V x.1) + H.compLpL 2 (cellMeasure d) x.2 :
    ChannelField d width) : PeriodicCell d → Channels width) =ᵐ[cellMeasure d] _
  filter_upwards [Lp.coeFn_add (Lp.const 2 (cellMeasure d) (V x.1))
      (H.compLpL 2 (cellMeasure d) x.2),
    Lp.coeFn_const (p := 2) (μ := cellMeasure d) (c := V x.1),
    H.coeFn_compLpL x.2] with y hadd hconstant hfield
  rw [hadd, Pi.add_apply, hconstant, hfield]
  change L (x.1, 0) + L (0, x.2 y) = L (x.1, x.2 y)
  simpa using (L.map_add (x.1, 0) (0, x.2 y)).symm

/-- Remark 4.3, information-preserving lifting: vector and field inputs
admit one injective continuous linear L² realization by the stated pointwise
linear lifting, with finite channel width. -/
theorem exists_injective_channel_lifting (d vectorInput functionInput : ℕ) :
    ∃ width : ℕ,
      ∃ S : WithLp 2 (Channels vectorInput × Channels functionInput) →ₗ[ℝ] Channels width,
        ∃ A : (Channels vectorInput × ChannelField d functionInput) →L[ℝ]
            ChannelField d width,
          Function.Injective A ∧
            ∀ x : Channels vectorInput × ChannelField d functionInput,
              (A x : PeriodicCell d → Channels width) =ᵐ[cellMeasure d]
                fun y => S (WithLp.toLp 2 (x.1, x.2 y)) := by
  classical
  let U := WithLp 2 (Channels vectorInput × Channels functionInput)
  let width := Module.finrank ℝ U
  let e : U ≃ₗ[ℝ] Channels width :=
    (Module.finBasis ℝ U).equivFun.trans
      (WithLp.linearEquiv 2 ℝ (Fin width → ℝ)).symm
  obtain ⟨A, hA⟩ := exists_channel_liftingCLM (d := d) e.toLinearMap
  refine ⟨width, e.toLinearMap, A, ?_, hA⟩
  intro x z hxz
  have hae : ∀ᵐ y ∂cellMeasure d, (x.1, x.2 y) = (z.1, z.2 y) := by
    filter_upwards [hA x, hA z] with y hx hz
    have he : e (WithLp.toLp 2 (x.1, x.2 y)) =
        e (WithLp.toLp 2 (z.1, z.2 y)) :=
      hx.symm.trans ((congrArg (fun q : ChannelField d width => q y) hxz).trans hz)
    exact congrArg WithLp.ofLp (e.injective he)
  apply Prod.ext
  · obtain ⟨y, hy⟩ := hae.exists
    exact congrArg (fun p : Channels vectorInput × Channels functionInput => p.1) hy
  · apply Lp.ext
    exact hae.mono (fun y hy =>
      congrArg (fun p : Channels vectorInput × Channels functionInput => p.2) hy)


end KVApproximation.NeuralOperators
