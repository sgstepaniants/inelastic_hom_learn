module

public import KVApproximation.NeuralOperators.FourierMappingLipschitz
public import KVApproximation.NeuralOperators.FourierProjectionFeatures
public import KVApproximation.NeuralOperators.FourierFeatureLayer
public import KVApproximation.NeuralOperators.FourierProjectionEvaluation
public import KVApproximation.Approximation.VectorRidgeApproximation

/-!
# Universal approximation by the constant-bias Fourier architecture

An injective linear lifting and scalar Fourier observations separate the
compact input set. Finite ridge approximation supplies one Fourier layer;
a common finite observation recovers its continuous hidden field at the origin.
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis KVApproximation.Approximation

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, representatives: Fourier projection uses only the
almost-everywhere class of the hidden field. -/
private theorem projection_eval_congr_ae {d input output : ℕ}
    (P : FourierProjection d input output) {h g : PeriodicCell d → Channels input}
    (hfg : h =ᵐ[cellMeasure d] g) : P.eval h = P.eval g := by
  have hc (k : Fin d → ℤ) (j : Fin input) :
      channelFourier h k j = channelFourier g k j := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  simp only [FourierProjection.eval, FourierProjection.complexValue, hc]

/-- Remark 4.3 (`rmk:fnm_admissible`): the concrete Fourier mapping class
satisfies A1 for smooth, globally Lipschitz, non-polynomial activation. -/
theorem fourierMappingClass_universal {σ : ℝ → ℝ}
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σ) {K : NNReal} (hLip : LipschitzWith K σ)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σ x = p.eval x)
    (d vectorInput functionInput output : ℕ) :
    HasUniversalApproximation (fourierMappingClass σ d vectorInput functionInput output) := by
  classical
  intro V M hV hM g ε hε
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hM
  let inc : C(V × M, Channels vectorInput × ChannelField d functionInput) :=
    ⟨fun x => (x.1.val, x.2.val),
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)⟩
  obtain ⟨liftWidth, S, A, hinjective, hA⟩ :=
    exists_injective_channel_lifting d vectorInput functionInput
  let φ (P : FourierProjection d liftWidth 1) : C(V × M, ℝ) :=
    ⟨fun x => P.eval (A (inc x)) 0, by
      obtain ⟨B, hB⟩ := P.exists_evalCLM
      exact ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 1 => ℝ) 0).continuous.comp
        (B.continuous.comp (A.continuous.comp inc.continuous))).congr
          (fun x => congrArg (fun v : Channels 1 => v 0) (hB (A (inc x))))⟩
  have hsep : ∀ x y : V × M, x ≠ y →
      ∃ P : FourierProjection d liftWidth 1, φ P x ≠ φ P y := by
    intro x y hxy
    by_contra hnone
    push_neg at hnone
    have hfields : A (inc x) = A (inc y) :=
      eq_of_scalarFourierProjections_eq (fun P => hnone P)
    have hpairs := hinjective hfields
    apply hxy
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpairs)
    · exact Subtype.ext (congrArg Prod.snd hpairs)
  obtain ⟨features, obs, width, a, w, b, hridge⟩ :=
    exists_finite_feature_ridge_approximation φ hsep hSmooth hNonpoly output g (half_pos hε)
  obtain ⟨layer, hlocal, hbias, horigin⟩ := exists_fourier_feature_layer obs w b
  let hidden : C((V × M) × PeriodicCell d, Channels width) :=
    ⟨fun p => layer.eval σ (A (inc p.1)) p.2,
      (layer.continuous_eval_of_zero_localWeight hlocal hSmooth.continuous).comp
        ((A.continuous.comp (inc.continuous.comp continuous_fst)).prodMk continuous_snd)⟩
  have hhidden (x : V × M) : hidden (x, 0) =
      WithLp.toLp 2 (fun j => σ ((∑ i : Fin features, w j i * φ (obs i) x) + b j)) := by
    change layer.eval σ (A (inc x)) 0 = _
    simp [FourierLayer.eval, hlocal, hbias, horigin, φ]
  let R : Channels width →L[ℝ] Channels output :=
    ∑ j : Fin width, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin width => ℝ) j).smulRight (a j)
  have hR (z : Channels width) : R z = ∑ j : Fin width, z j • a j := by
    simp only [R, sum_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply]
  let δ := (ε / 2) / (‖R‖ + 1)
  have hden : 0 < ‖R‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos (half_pos hε) hden
  obtain ⟨Q, hQ⟩ := exists_fourierProjection_approx_eval hidden (0 : PeriodicCell d) hδ
  let network : FourierMapping d vectorInput functionInput output := {
    liftWidth := liftWidth
    hiddenWidth := width
    projectionWidth := width
    lifting := S
    layers := .cons layer (.nil width)
    projection := Q
    outputMap := R.toLinearMap }
  obtain ⟨C, hC⟩ := network.lipschitz hLip
  let Φ : C(Channels vectorInput × ChannelField d functionInput, Channels output) :=
    ⟨network.eval σ, hC.continuous⟩
  have hΦ (x : V × M) :
      Φ (inc x) = R (Q.eval (fun y => hidden (x, y))) := by
    change R (Q.eval (layer.eval σ
      (fun y => S (WithLp.toLp 2 ((inc x).1, (inc x).2 y))))) = _
    apply congrArg R
    exact (projection_eval_congr_ae Q (layer.eval_congr_ae σ (hA (inc x)))).symm
  have htarget (x : V × M) : ‖R (hidden (x, 0)) - g x‖ < ε / 2 := by
    rw [hhidden, hR]
    exact hridge x
  have hobserve (x : V × M) :
      ‖R (Q.eval (fun y => hidden (x, y))) - R (hidden (x, 0))‖ ≤ ε / 2 := by
    calc
      _ = ‖R (Q.eval (fun y => hidden (x, y)) - hidden (x, 0))‖ :=
        congrArg norm (R.map_sub _ _).symm
      _ ≤ ‖R‖ * ‖Q.eval (fun y => hidden (x, y)) - hidden (x, 0)‖ := R.le_opNorm _
      _ ≤ ‖R‖ * δ := mul_le_mul_of_nonneg_left (hQ x).le (norm_nonneg R)
      _ ≤ (‖R‖ + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 2 := mul_div_cancel₀ (ε / 2) hden.ne'
  refine ⟨Φ, ⟨network, fun _ => rfl⟩, fun v m => ?_⟩
  let x : V × M := (v, m)
  change ‖Φ (inc x) - g x‖ ≤ ε
  rw [hΦ]
  calc
    _ ≤ ‖R (Q.eval (fun y => hidden (x, y))) - R (hidden (x, 0))‖ +
        ‖R (hidden (x, 0)) - g x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hobserve x) (htarget x).le
    _ = ε := add_halves ε

/-- Remark 4.3: the same concrete class satisfies the locally Lipschitz
universal-approximation property A2. -/
theorem fourierMappingClass_locallyLipschitz_universal {σ : ℝ → ℝ}
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σ) {K : NNReal} (hLip : LipschitzWith K σ)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σ x = p.eval x)
    (d vectorInput functionInput output : ℕ) :
    HasLocallyLipschitzApproximation
      (fourierMappingClass σ d vectorInput functionInput output) := by
  intro V M hV hM g ε hε
  obtain ⟨Φ, hΦ, herror⟩ :=
    fourierMappingClass_universal hSmooth hLip hNonpoly d vectorInput functionInput output
      V M hV hM g ε hε
  obtain ⟨P, hP⟩ := hΦ
  obtain ⟨C, hC⟩ := P.lipschitz hLip
  refine ⟨Φ, ⟨P, hP⟩, herror, ?_⟩
  intro m hm
  have heq : (fun v : Channels vectorInput => Φ (v, m)) =
      fun v => P.eval σ (v, m) := funext (fun v => hP (v, m))
  rw [heq]
  exact (hC.comp (LipschitzWith.id.prodMk (LipschitzWith.const m))).locallyLipschitz

end KVApproximation.NeuralOperators
