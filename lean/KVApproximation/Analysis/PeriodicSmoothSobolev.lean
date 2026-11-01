module

public import KVApproximation.Analysis.PeriodicSobolevDensity

/-!
# C¹ periodic fields in the Sobolev space

Periodic integration by parts gives the weak gradient. The completed-jet
characterization then supplies the actual periodic H¹ element.
-/

public section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Theorem 3.1, periodic flux tests: a C¹ periodic displacement is an
actual periodic H¹ element, with its prescribed value and full gradient. -/
theorem PeriodicC1.exists_periodicH1 {d : ℕ}
    (φ : PeriodicC1 d (EuclideanSpace ℝ (Fin d))) :
    ∃ u : PeriodicH1 d,
      (PeriodicH1.valueL d u =ᵐ[cellMeasure d] φ.value) ∧
      (PeriodicH1.gradientL d u =ᵐ[cellMeasure d] periodicGradient φ.value) := by
  let V : C(PeriodicCell d, EuclideanSpace ℝ (Fin d)) := ⟨φ.value, φ.continuous_value⟩
  have hc : Continuous (periodicGradient φ.value) := by
    change Continuous (fun y => WithLp.toLp 2 (fun ij : Fin d × Fin d => φ.partial ij.2 y ij.1))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d × Fin d => ℝ)).comp
      (continuous_pi fun ij => (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) ij.1).comp
        (φ.continuous_partial ij.2))
  let G : C(PeriodicCell d, SecondOrder d) := ⟨periodicGradient φ.value, hc⟩
  have hv : V.toLp 2 (cellMeasure d) ℝ =ᵐ[cellMeasure d] φ.value :=
    V.coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d)
  have hg : G.toLp 2 (cellMeasure d) ℝ =ᵐ[cellMeasure d] periodicGradient φ.value :=
    G.coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d)
  have hw : HasPeriodicWeakGradient (V.toLp 2 (cellMeasure d) ℝ)
      (G.toLp 2 (cellMeasure d) ℝ) := by
    intro ψ i j
    let P := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin d => ℝ) i
    have h₁ : Integrable (fun y => ψ.partial j y • φ.value y) (cellMeasure d) :=
      ((ψ.continuous_partial j).smul φ.continuous_value).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h₂ : Integrable (fun y => ψ.value y • φ.partial j y) (cellMeasure d) :=
      (ψ.continuous_value.smul (φ.continuous_partial j)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hp := congrArg P (φ.integral_smul_partial ψ j)
    rw [map_neg, ← P.integral_comp_comm h₁, ← P.integral_comp_comm h₂] at hp
    change (∫ y, ψ.partial j y * φ.value y i ∂cellMeasure d) =
      -(∫ y, ψ.value y * periodicGradient φ.value y (i, j) ∂cellMeasure d) at hp
    calc
      _ = ∫ y, ψ.partial j y * φ.value y i ∂cellMeasure d := by
        apply integral_congr_ae
        filter_upwards [hv] with y hy
        rw [hy, mul_comm]
      _ = -(∫ y, ψ.value y * periodicGradient φ.value y (i, j) ∂cellMeasure d) := hp
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hg] with y hy
        rw [hy, mul_comm]
  obtain ⟨u, hu, hgu⟩ := (periodicH1_iff_weakGradient _ _).mp hw
  exact ⟨u, hu ▸ hv, hgu ▸ hg⟩

end KVApproximation.Analysis
