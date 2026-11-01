module

public import KVApproximation.Analysis.TimeSobolevMemory
public import KVApproximation.Analysis.OperatorConvolutionBalance

/-!
# Sobolev memory equations from Green convolutions
-/

public section

open MeasureTheory Set

namespace KVApproximation.Analysis

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), forced weak equation:
an H¹ realization of the Green convolution has zero initial value and
satisfies the memory equation almost everywhere on one common full-measure set. -/
theorem TimeH1.memory_equation_of_green_trace
    {F H Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {T : ℝ} (hT : 0 < T) (u : TimeH1 H T)
    (V E : H →L[ℝ] Y) (K : ℝ → H →L[ℝ] Y)
    (G : ℝ → F →L[ℝ] H) (B : F →L[ℝ] Y)
    (hK : Continuous K) (hG : Continuous G)
    (hbalance : ∀ (t : ℝ), 0 ≤ t → ∀ g : F,
      V (G t g) + E (∫ s in (0 : ℝ)..t, G s g) +
        (∫ s in (0 : ℝ)..t, K (t - s) (G s g)) = B g)
    (f : ℝ → F) (hf : IntervalIntegrable f volume 0 T)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T,
      TimeH1.trace hT u t = ∫ r in (0 : ℝ)..(t : ℝ), G ((t : ℝ) - r) (f r)) :
    TimeH1.initial hT u = 0 ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        V (TimeH1.velocity u t) + E (TimeH1.value u t) +
          posConvolution K (TimeH1.velocity u)
            (ContinuousLinearMap.id ℝ (H →L[ℝ] Y)) volume t = B (f t) := by
  let q : ℝ → H := fun r => TimeH1.trace hT u (projIcc 0 T hT.le r)
  let p : ℝ → H := fun t => ∫ r in (0 : ℝ)..t, G (t - r) (f r)
  have hq (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) : q r = p r := by
    simpa only [q, p, projIcc_of_mem hT.le hr] using htrace ⟨r, hr⟩
  have hinit : TimeH1.initial hT u = 0 := by
    change TimeH1.trace hT u ⟨0, le_rfl, hT.le⟩ = 0
    simpa only [intervalIntegral.integral_same] using htrace ⟨0, le_rfl, hT.le⟩
  have hforce : IntervalIntegrable (fun t => B (f t)) volume 0 T :=
    ⟨B.integrable_comp hf.1, B.integrable_comp hf.2⟩
  refine ⟨hinit, (TimeH1.memory_equation_iff_integrated hT u V E
    (ContinuousLinearMap.id ℝ (H →L[ℝ] Y)) K hK (fun t => B (f t)) hforce).mpr ?_⟩
  change ∀ t : Icc (0 : ℝ) T,
    V (q t - TimeH1.initial hT u) + E (∫ r in (0 : ℝ)..(t : ℝ), q r) +
      posConvolution K (fun r => q r - TimeH1.initial hT u)
        (ContinuousLinearMap.id ℝ (H →L[ℝ] Y)) volume t =
          ∫ r in (0 : ℝ)..(t : ℝ), B (f r)
  intro t
  have hsub (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) (t : ℝ)) : r ∈ Icc (0 : ℝ) T := by
    rw [uIcc_of_le t.property.1] at hr
    exact ⟨hr.1, hr.2.trans t.property.2⟩
  have hprimitive : (∫ r in (0 : ℝ)..(t : ℝ), q r) = ∫ r in (0 : ℝ)..(t : ℝ), p r :=
    intervalIntegral.integral_congr fun r hr => hq r (hsub r hr)
  have hmemory : posConvolution K (fun r => q r - TimeH1.initial hT u)
      (ContinuousLinearMap.id ℝ (H →L[ℝ] Y)) volume t =
        ∫ r in (0 : ℝ)..(t : ℝ), K ((t : ℝ) - r) (p r) := by
    rw [posConvolution_eq_integral_sub
      (ContinuousLinearMap.id ℝ (H →L[ℝ] Y)) K _ t.property.1]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    rw [ContinuousLinearMap.id_apply, hinit, sub_zero, hq r (hsub r hr)]
  rw [hmemory, hinit, sub_zero, hq t t.property, hprimitive]
  exact duhamel_integrated_memory_balance V E K G B hK hG hbalance f hf t t.property

end KVApproximation.Analysis
