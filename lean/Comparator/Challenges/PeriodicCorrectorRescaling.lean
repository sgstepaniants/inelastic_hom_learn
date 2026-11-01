module

public import KVApproximation.Analysis.PeriodicAveragingReal
public import KVApproximation.Analysis.PeriodicGradientMean
public import KVApproximation.Analysis.VectorSobolevProperties

public section

open MeasureTheory Filter TopologicalSpace
open KVApproximation.Tensor
open scoped Topology

namespace KVApproximation.Analysis

/-- Theorem 3.1, oscillating correctors: multiplying a rescaled periodic
L² field by its scale gives strong L² convergence to zero. -/
theorem tendsto_eLpNorm_smul_rescalePeriodic_zero {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (PhysicalSpace d)} (hΩ : Bornology.IsBounded Ω)
    {f : PeriodicCell d → F} (hf : MemLp f 2 (cellMeasure d)) :
    Tendsto (fun ε : ℝ =>
      eLpNorm (fun x => ε • rescalePeriodic f ε x) 2 (volume.restrict Ω))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry

/-- Theorem 3.1, oscillating corrector tests: the scaled periodic
displacement belongs to physical H¹ and its weak gradient is the
rescaled periodic gradient, with both identities holding almost everywhere. -/
theorem PeriodicH1.exists_rescaled {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (u : PeriodicH1 d) :
    ∃ v : VectorH1 Ω,
      (VectorH1.valueL Ω v =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        fun x => ε • rescalePeriodic (PeriodicH1.valueL d u) ε x) ∧
      (VectorH1.gradientL Ω v =ᵐ[volume.restrict (Ω : Set (PhysicalSpace d))]
        rescalePeriodic (PeriodicH1.gradientL d u) ε) := by
  sorry

/-- Theorem 3.1, oscillating correctors: periodic gradients converge
weakly to zero after rescaling, since their normalized cell mean is zero. -/
theorem PeriodicH1.tendsto_integral_rescale_gradient_inner {d : ℕ}
    {Ω : Set (PhysicalSpace d)} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) (u : PeriodicH1 d)
    {g : PhysicalSpace d → SecondOrder d} (hg : MemLp g 2 (volume.restrict Ω)) :
    Tendsto (fun ε : ℝ =>
      ∫ x in Ω, inner ℝ (rescalePeriodic (PeriodicH1.gradientL d u) ε x) (g x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry

end KVApproximation.Analysis
