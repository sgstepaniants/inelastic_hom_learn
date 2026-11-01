module

public import KVApproximation.Analysis.PeriodicVariation
public import KVApproximation.Analysis.PeriodicSmoothIdentities
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Stability of periodic total variation

The distributional tests are continuous on L¹ because their divergences are
continuous on the compact cell. Passing each test to the limit preserves the
full BV norm bound used in Lemma B.2.
-/

public section

open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

namespace KVApproximation.Analysis

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Section 4.1 (`eq:TV_tensor`): the divergence of a smooth periodic
test field is continuous on the cell. -/
theorem PeriodicC1.continuous_divergence
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F))) :
    Continuous φ.divergence := by
  apply continuous_finsetSum
  intro i _
  exact (PiLp.continuous_apply 2 (fun _ : Fin d => F) i).comp
    (φ.continuous_partial i)

/-- Lemma B.2, lower semicontinuity: each distributional variation test
is a continuous scalar functional of the L¹ coefficient field. -/
theorem continuous_periodicTestPairing
    (φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F))) :
    Continuous (fun A : Lp F 1 (cellMeasure d) =>
      ∫ y, ⟪A y, φ.divergence y⟫_ℝ ∂cellMeasure d) := by
  let g : C(PeriodicCell d, F) := ⟨φ.divergence, φ.continuous_divergence⟩
  let G : Lp F ∞ (cellMeasure d) := ContinuousMap.toLp ∞ (cellMeasure d) ℝ g
  let L : Lp F 1 (cellMeasure d) →L[ℝ] ℝ :=
    ((innerSL ℝ (E := F)).lpPairing (cellMeasure d) 1 ∞).flip G
  convert L.continuous using 1
  funext A
  change (∫ y, ⟪A y, φ.divergence y⟫_ℝ ∂cellMeasure d) =
    (innerSL ℝ (E := F)).lpPairing (cellMeasure d) 1 ∞ A G
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℝ) (cellMeasure d) g]
    with y hy
  change ⟪A y, φ.divergence y⟫_ℝ = ⟪A y, G y⟫_ℝ
  exact congrArg (fun z => ⟪A y, z⟫_ℝ) hy.symm

/-- Section 4.1 (`eq:TV_tensor`): periodic variation depends only on the
almost-everywhere equivalence class. -/
theorem periodicVariation_congr {A B : PeriodicCell d → F}
    (h : A =ᵐ[cellMeasure d] B) : periodicVariation A = periodicVariation B := by
  unfold periodicVariation
  apply iSup_congr
  intro φ
  apply iSup_congr
  intro _
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

/-- Section 4.1 (`eq:bv_bound_microstructure`): the periodic BV norm is
independent of the chosen almost-everywhere representative. -/
theorem periodicBVNorm_congr {A B : PeriodicCell d → F}
    (h : A =ᵐ[cellMeasure d] B) : periodicBVNorm A = periodicBVNorm B := by
  unfold periodicBVNorm
  rw [eLpNorm_congr_ae h, periodicVariation_congr h]

/-- Lemma B.2 (`lem:bv_compact`), lower semicontinuity: a common BV norm
bound is preserved under L¹ convergence on the periodic cell. -/
theorem periodicBVNorm_le_of_tendsto_L1
    {A : Lp F 1 (cellMeasure d)} {Aseq : ℕ → Lp F 1 (cellMeasure d)} {C : ENNReal}
    (hconv : Tendsto Aseq atTop (𝓝 A))
    (hbound : ∀ n, periodicBVNorm (Aseq n) ≤ C) : periodicBVNorm A ≤ C := by
  have htest : ∃ φ : PeriodicC1 d (PiLp 2 (fun _ : Fin d => F)),
      ∀ y, ‖φ.value y‖ ≤ 1 :=
    ⟨⟨fun _ => 0, contDiff_const⟩, fun _ => by simp⟩
  rw [periodicBVNorm, periodicVariation, ENNReal.add_biSup' htest]
  apply iSup₂_le
  intro φ hφ
  have hnorm : Tendsto (fun n => eLpNorm (Aseq n) 1 (cellMeasure d)) atTop
      (𝓝 (eLpNorm A 1 (cellMeasure d))) := by
    simpa only [← Lp.enorm_def, Function.comp_def] using
      continuous_enorm.tendsto A |>.comp hconv
  have hpair := (continuous_periodicTestPairing φ).tendsto A |>.comp hconv
  apply le_of_tendsto (hnorm.add (ENNReal.continuous_ofReal.tendsto _ |>.comp hpair))
  apply Eventually.of_forall
  intro n
  change eLpNorm (Aseq n) 1 (cellMeasure d) +
    ENNReal.ofReal (∫ y, ⟪Aseq n y, φ.divergence y⟫_ℝ ∂cellMeasure d) ≤ C
  apply le_trans (b := periodicBVNorm (Aseq n)) _ (hbound n)
  apply add_le_add_right
  exact le_iSup_of_le φ (le_iSup_of_le hφ le_rfl)

end KVApproximation.Analysis
