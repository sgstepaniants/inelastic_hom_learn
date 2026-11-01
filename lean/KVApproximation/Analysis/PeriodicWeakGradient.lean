module

public import KVApproximation.Analysis.PeriodicIntegration
public import KVApproximation.Analysis.PeriodicSobolev
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weak derivatives of completed periodic jets
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

private def testPairingL {d : ℕ} (a : C(PeriodicCell d, ℝ))
    (L : PeriodicJet d →L[ℝ] ℝ) : PeriodicJetField d →L[ℝ] ℝ :=
  ((ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).lpPairing (cellMeasure d) 2 2
    (ContinuousMap.toLp 2 (cellMeasure d) ℝ a)).comp (L.compLpL 2 (cellMeasure d))

private theorem testPairingL_eq_integral {d : ℕ} (a : C(PeriodicCell d, ℝ))
    (L : PeriodicJet d →L[ℝ] ℝ) (u : PeriodicJetField d) :
    testPairingL a L u = ∫ y, a y * L (u y) ∂cellMeasure d := by
  rw [testPairingL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (cellMeasure d) (𝕜 := ℝ) a,
    L.coeFn_compLpL u] with y ha hL
  change (ContinuousMap.toLp 2 (cellMeasure d) ℝ a) y *
    (L.compLpL 2 (cellMeasure d) u) y = _
  rw [ha, hL]

/-- Section 3.1: completed smooth periodic jets satisfy the weak derivative identity. -/
theorem PeriodicH1.hasWeakGradient {d : ℕ} (u : PeriodicH1 d) :
    HasPeriodicWeakGradient (PeriodicH1.valueL d u) (PeriodicH1.gradientL d u) := by
  intro φ i j
  let V : PeriodicJet d →L[ℝ] ℝ :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i).comp
      (WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d))
  let G : PeriodicJet d →L[ℝ] ℝ :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d × Fin d => ℝ) (i, j)).comp
      (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d))
  let a : C(PeriodicCell d, ℝ) := ⟨φ.partial j, φ.continuous_partial j⟩
  let b : C(PeriodicCell d, ℝ) := ⟨φ.value, φ.continuous_value⟩
  let T : PeriodicJetField d →L[ℝ] ℝ := testPairingL a V + testPairingL b G
  let K : ClosedSubmodule ℝ (PeriodicJetField d) :=
    (⊥ : ClosedSubmodule ℝ ℝ).comap T
  have hle : periodicH1Submodule d ≤ K := by
    apply Submodule.closure_le.mpr
    apply Submodule.span_le.mpr
    rintro w ⟨ψ, hψ, hw⟩
    let χ : PeriodicC1 d (EuclideanSpace ℝ (Fin d)) := ⟨ψ, hψ.of_le (by simp)⟩
    let P := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i
    have h₁ : Integrable (fun y => φ.partial j y • χ.value y) (cellMeasure d) :=
      ((φ.continuous_partial j).smul χ.continuous_value).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h₂ : Integrable (fun y => φ.value y • χ.partial j y) (cellMeasure d) :=
      (φ.continuous_value.smul (χ.continuous_partial j)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hparts := congrArg P (χ.integral_smul_partial φ j)
    rw [map_neg, ← P.integral_comp_comm h₁, ← P.integral_comp_comm h₂] at hparts
    change (∫ y, φ.partial j y * ψ y i ∂cellMeasure d) =
      -(∫ y, φ.value y * periodicGradient ψ y (i, j) ∂cellMeasure d) at hparts
    change T w = 0
    change testPairingL a V w + testPairingL b G w = 0
    rw [testPairingL_eq_integral, testPairingL_eq_integral]
    have hv : (∫ y, a y * V (w y) ∂cellMeasure d) =
        ∫ y, φ.partial j y * ψ y i ∂cellMeasure d := by
      apply integral_congr_ae
      filter_upwards [hw] with y hy
      rw [hy]
      rfl
    have hg : (∫ y, b y * G (w y) ∂cellMeasure d) =
        ∫ y, φ.value y * periodicGradient ψ y (i, j) ∂cellMeasure d := by
      apply integral_congr_ae
      filter_upwards [hw] with y hy
      rw [hy]
      rfl
    rw [hv, hg, hparts, neg_add_cancel]
  have hu : T u.val = 0 := hle u.property
  change testPairingL a V u.val + testPairingL b G u.val = 0 at hu
  rw [testPairingL_eq_integral, testPairingL_eq_integral] at hu
  have hv : (∫ y, PeriodicH1.valueL d u y i * φ.partial j y ∂cellMeasure d) =
      ∫ y, a y * V (u.val y) ∂cellMeasure d := by
    apply integral_congr_ae
    filter_upwards
      [(WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL u.val]
        with y hy
    change (((WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).compLpL
      2 (cellMeasure d) u.val) y) i * φ.partial j y = _
    rw [hy]
    exact mul_comm _ _
  have hg : (∫ y, PeriodicH1.gradientL d u y (i, j) * φ.value y ∂cellMeasure d) =
      ∫ y, b y * G (u.val y) ∂cellMeasure d := by
    apply integral_congr_ae
    filter_upwards
      [(WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL u.val]
        with y hy
    change (((WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).compLpL
      2 (cellMeasure d) u.val) y) (i, j) * φ.value y = _
    rw [hy]
    exact mul_comm _ _
  rw [hv, hg]
  exact eq_neg_of_add_eq_zero_left hu

end KVApproximation.Analysis
