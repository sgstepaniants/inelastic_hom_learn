module

public import KVApproximation.Analysis.TimeSobolevMemory
public import KVApproximation.Analysis.LaplaceMemory

/-!
# Sobolev memory equations from half-line Laplace transforms

Only the closed finite-horizon trace is identified with the half-line
extension. Differentiation then recovers one vector-valued weak equation.
-/

public section

open MeasureTheory Set

namespace KVApproximation.Analysis

/-- Theorem 3.1 (`thm:viscoelastic_homogenization`), weak-equation
recovery: a bounded continuous half-line extension of the Sobolev trace and
its prepared transformed equation imply the memory balance almost everywhere,
on one common full-measure set of times. -/
theorem TimeH1.memory_equation_of_halfLineLaplace
    {H F G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {T : ℝ} (hT : 0 < T) (u : TimeH1 H T)
    (v : ℝ → H) (hv : ContinuousOn v (Set.Ici (0 : ℝ))) {M : ℝ}
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ M)
    (htrace : ∀ t : Set.Icc (0 : ℝ) T, TimeH1.trace hT u t = v t)
    (V E : H →L[ℝ] G) (L : F →L[ℝ] H →L[ℝ] G)
    (K : ℝ → F) (hK : Continuous K)
    (hKi : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun t => Real.exp (-s * t) • K t) (Set.Ioi (0 : ℝ)))
    (hLap : ∀ s : ℝ, 0 < s →
      (V + s⁻¹ • E + L (halfLineLaplace K s))
        (s • halfLineLaplace v s - TimeH1.initial hT u) =
          -s⁻¹ • E (TimeH1.initial hT u)) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      V (TimeH1.velocity u t) + E (TimeH1.value u t) +
        posConvolution K (TimeH1.velocity u) L volume t = 0 := by
  have hbalance := integrated_memory_eq_zero_of_halfLineLaplace
    V E L K hK hKi v hv hbound (TimeH1.initial hT u) hLap
  let q : ℝ → H := fun r => TimeH1.trace hT u (Set.projIcc 0 T hT.le r)
  have hq (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) : q r = v r := by
    simpa only [q, projIcc_of_mem hT.le hr] using htrace ⟨r, hr⟩
  apply (TimeH1.memory_equation_iff_integrated hT u V E L K hK
    (fun _ => (0 : G)) intervalIntegrable_const).mpr
  change ∀ t : Icc (0 : ℝ) T,
    V (q t - TimeH1.initial hT u) + E (∫ r in (0 : ℝ)..(t : ℝ), q r) +
      posConvolution K (fun r => q r - TimeH1.initial hT u) L volume t =
        ∫ r in (0 : ℝ)..(t : ℝ), (0 : G)
  intro t
  have hrT (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) (t : ℝ)) : r ∈ Icc (0 : ℝ) T := by
    rw [uIcc_of_le t.property.1] at hr
    exact ⟨hr.1, hr.2.trans t.property.2⟩
  have hprim : (∫ r in (0 : ℝ)..(t : ℝ), q r) = ∫ r in (0 : ℝ)..(t : ℝ), v r :=
    intervalIntegral.integral_congr fun r hr => hq r (hrT r hr)
  have hconv : posConvolution K (fun r => q r - TimeH1.initial hT u) L volume t =
      posConvolution K (fun r => v r - TimeH1.initial hT u) L volume t := by
    rw [posConvolution_eq_integral_sub _ _ _ t.property.1,
      posConvolution_eq_integral_sub _ _ _ t.property.1]
    apply intervalIntegral.integral_congr
    intro r hr
    exact congrArg (fun z => L (K ((t : ℝ) - r)) (z - TimeH1.initial hT u))
      (hq r (hrT r hr))
  rw [hq t t.property, hprim, hconv, intervalIntegral.integral_zero]
  exact hbalance t t.property.1

end KVApproximation.Analysis
