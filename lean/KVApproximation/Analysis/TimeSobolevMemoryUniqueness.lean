module

public import KVApproximation.Analysis.TimeSobolevMemory
public import KVApproximation.Analysis.TimeSobolevMaps
public import KVApproximation.Analysis.VolterraUniqueness

/-!
# Uniqueness of Sobolev trajectories with memory

Subtracting the integrated trace equations reduces weak uniqueness to the
continuous Volterra equation on the same finite interval.
-/

public section

open MeasureTheory Set

namespace KVApproximation.Analysis

variable {H F G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Theorem 3.1, finite-time weak uniqueness: two Sobolev trajectories
with the same initial value and forcing coincide under the viscous norm bound.
Both competitors are defined only on the stated finite horizon. -/
theorem TimeH1.eq_of_memory_equation {T : ℝ} (hT : 0 < T)
    (u v : TimeH1 H T) (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K) (g : ℝ → G)
    (hg : IntervalIntegrable g volume 0 T) (c : ℝ) (hc : 0 ≤ c)
    (hV : ∀ x : H, ‖x‖ ≤ c * ‖V x‖)
    (hinit : TimeH1.initial hT u = TimeH1.initial hT v)
    (hu : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      V (TimeH1.velocity u t) + E (TimeH1.value u t) +
        posConvolution K (TimeH1.velocity u) L volume t = g t)
    (hv : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      V (TimeH1.velocity v t) + E (TimeH1.value v t) +
        posConvolution K (TimeH1.velocity v) L volume t = g t) : u = v := by
  let qu : ℝ → H := fun t => TimeH1.trace hT u (projIcc 0 T hT.le t)
  let qv : ℝ → H := fun t => TimeH1.trace hT v (projIcc 0 T hT.le t)
  have hqu : Continuous qu := (TimeH1.trace hT u).continuous.comp continuous_projIcc
  have hqv : Continuous qv := (TimeH1.trace hT v).continuous.comp continuous_projIcc
  have hui := (TimeH1.memory_equation_iff_integrated hT u V E L K hK g hg).mp hu
  have hvi := (TimeH1.memory_equation_iff_integrated hT v V E L K hK g hg).mp hv
  let w : ℝ → H := fun t => qu t - qv t
  have hw : Continuous w := hqu.sub hqv
  have hbalance (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      V (w t) + E (∫ r in (0 : ℝ)..t, w r) + posConvolution K w L volume t = 0 := by
    have hmemory : posConvolution K w L volume t =
        posConvolution K (fun r => qu r - TimeH1.initial hT u) L volume t -
          posConvolution K (fun r => qv r - TimeH1.initial hT v) L volume t := by
      rw [posConvolution_eq_integral_sub L K _ ht.1,
        posConvolution_eq_integral_sub L K _ ht.1,
        posConvolution_eq_integral_sub L K _ ht.1]
      have heq : (fun r => L (K (t - r)) (w r)) =
          fun r => L (K (t - r)) (qu r - TimeH1.initial hT u) -
            L (K (t - r)) (qv r - TimeH1.initial hT v) := by
        funext r
        rw [← map_sub]
        congr 1
        dsimp only [w]
        rw [hinit]
        abel
      rw [heq]
      exact intervalIntegral.integral_sub
        (intervalIntegrable_posConvolution_integrand L K _ hK
          ((hqu.sub continuous_const).intervalIntegrable 0 T) ht)
        (intervalIntegrable_posConvolution_integrand L K _ hK
          ((hqv.sub continuous_const).intervalIntegrable 0 T) ht)
    have hvisc : V (w t) = V (qu t - TimeH1.initial hT u) -
        V (qv t - TimeH1.initial hT v) := by
      rw [← map_sub]
      congr 1
      dsimp only [w]
      rw [hinit]
      abel
    have hprimitive : (∫ r in (0 : ℝ)..t, w r) =
        (∫ r in (0 : ℝ)..t, qu r) - ∫ r in (0 : ℝ)..t, qv r :=
      intervalIntegral.integral_sub (hqu.intervalIntegrable 0 t) (hqv.intervalIntegrable 0 t)
    rw [hmemory, hvisc, hprimitive, E.map_sub]
    calc
      _ = (V (qu t - TimeH1.initial hT u) + E (∫ r in (0 : ℝ)..t, qu r) +
          posConvolution K (fun r => qu r - TimeH1.initial hT u) L volume t) -
        (V (qv t - TimeH1.initial hT v) + E (∫ r in (0 : ℝ)..t, qv r) +
          posConvolution K (fun r => qv r - TimeH1.initial hT v) L volume t) := by abel
      _ = 0 := by rw [hui ⟨t, ht⟩, hvi ⟨t, ht⟩, sub_self]
  have hwzero := eqOn_zero_of_integrated_memory_eq_zero hT.le w hw.continuousOn
    V E L K hK c hc hV hbalance
  apply TimeH1.eq_of_value_ae
  filter_upwards [TimeH1.trace_ae hT u, TimeH1.trace_ae hT v,
    ae_restrict_mem measurableSet_Ioo] with t htu htv ht
  have hz : qu t - qv t = 0 := hwzero ⟨ht.1.le, ht.2.le⟩
  exact htu.trans ((sub_eq_zero.mp hz).trans htv.symm)

end KVApproximation.Analysis
