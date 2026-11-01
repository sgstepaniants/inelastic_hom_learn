module

public import KVApproximation.NeuralOperators.FourierMapping
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Admissibility of the Fourier neural mapping
-/

public section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1: a globally Lipschitz activation preserves L² in each layer. -/
theorem FourierLayer.memLp_eval {d input output : ℕ} (L : FourierLayer d input output)
    {σ : ℝ → ℝ} {K : NNReal} (hσ : LipschitzWith K σ)
    {h : PeriodicCell d → Channels input} (hh : MemLp h 2 (cellMeasure d)) :
    MemLp (L.eval σ h) 2 (cellMeasure d) := by
  sorry

/-- Example 2.1: layer evaluation respects equality almost everywhere. -/
theorem FourierLayer.eval_congr_ae {d input output : ℕ} (L : FourierLayer d input output)
    (σ : ℝ → ℝ) {h g : PeriodicCell d → Channels input}
    (hfg : h =ᵐ[cellMeasure d] g) : L.eval σ h =ᵐ[cellMeasure d] L.eval σ g := by
  sorry

/-- Example 2.1: every finite chain preserves L² for a globally Lipschitz activation. -/
theorem FourierChain.memLp_eval {d input output : ℕ} (L : FourierChain d input output)
    {σ : ℝ → ℝ} {K : NNReal} (hσ : LipschitzWith K σ)
    {h : PeriodicCell d → Channels input} (hh : MemLp h 2 (cellMeasure d)) :
    MemLp (L.eval σ h) 2 (cellMeasure d) := by
  sorry

/-- Example 2.1: finite chains respect equality almost everywhere. -/
theorem FourierChain.eval_congr_ae {d input output : ℕ} (L : FourierChain d input output)
    (σ : ℝ → ℝ) {h g : PeriodicCell d → Channels input}
    (hfg : h =ᵐ[cellMeasure d] g) : L.eval σ h =ᵐ[cellMeasure d] L.eval σ g := by
  sorry

/-- Example 2.1: conjugate symmetry of the retained modes and matrices
makes the Fourier layer real-valued on real L² fields. -/
theorem FourierLayer.fourierPart_im {d input output : ℕ} (L : FourierLayer d input output)
    (h : PeriodicCell d → Channels input) (hh : MemLp h 2 (cellMeasure d))
    (y : PeriodicCell d) (i : Fin output) : (L.fourierPart h y i).im = 0 := by
  sorry

/-- Example 2.1: the conjugate-symmetric Fourier projection is real-valued. -/
theorem FourierProjection.complexValue_im {d input output : ℕ}
    (P : FourierProjection d input output) (h : PeriodicCell d → Channels input)
    (hh : MemLp h 2 (cellMeasure d)) (i : Fin output) :
    (P.complexValue h i).im = 0 := by
  sorry

/-- Example 2.1: the full mapping does not depend on the L² representative. -/
theorem FourierMapping.evalRepresentative_congr {d vectorInput functionInput output : ℕ}
    (P : FourierMapping d vectorInput functionInput output) (σ : ℝ → ℝ)
    (v : Channels vectorInput) {h g : PeriodicCell d → Channels functionInput}
    (hfg : h =ᵐ[cellMeasure d] g) :
    P.evalRepresentative σ v h = P.evalRepresentative σ v g := by
  sorry

/-- Remark 4.3: globally Lipschitz activations make every finite mapping
globally Lipschitz on the full L² input space, hence continuous and locally
Lipschitz in its vector input. -/
theorem FourierMapping.lipschitz {d vectorInput functionInput output : ℕ}
    (P : FourierMapping d vectorInput functionInput output) {σ : ℝ → ℝ}
    {K : NNReal} (hσ : LipschitzWith K σ) :
    ∃ L : NNReal, LipschitzWith L (P.eval σ) := by
  sorry

/-- Remark 4.3 (`rmk:fnm_admissible`): the concrete Fourier mapping class
satisfies A1 for smooth, globally Lipschitz, non-polynomial activation. -/
theorem fourierMappingClass_universal {σ : ℝ → ℝ}
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σ) {K : NNReal} (hLip : LipschitzWith K σ)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σ x = p.eval x)
    (d vectorInput functionInput output : ℕ) :
    HasUniversalApproximation (fourierMappingClass σ d vectorInput functionInput output) := by
  sorry

/-- Remark 4.3: the same concrete class satisfies the locally Lipschitz
universal-approximation property A2. -/
theorem fourierMappingClass_locallyLipschitz_universal {σ : ℝ → ℝ}
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) σ) {K : NNReal} (hLip : LipschitzWith K σ)
    (hNonpoly : ¬ ∃ p : Polynomial ℝ, ∀ x : ℝ, σ x = p.eval x)
    (d vectorInput functionInput output : ℕ) :
    HasLocallyLipschitzApproximation
      (fourierMappingClass σ d vectorInput functionInput output) := by
  sorry

end KVApproximation.NeuralOperators
