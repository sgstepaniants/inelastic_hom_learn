module

public import KVApproximation.NeuralOperators.FourierMapping
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# L² preservation by Fourier neural layers
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1, activation step: on a finite measure space a globally
Lipschitz activation preserves L² without fixing zero. -/
private theorem activation_comp_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {σ : ℝ → ℝ} {K : NNReal}
    (hσ : LipschitzWith K σ) {f : X → ℝ} (hf : MemLp f 2 μ) :
    MemLp (fun x => σ (f x)) 2 μ := by
  have hc : LipschitzWith K (fun x => σ x - σ 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hσ.dist_le_mul x y
  have hcenter := hc.comp_memLp (sub_self (σ 0)) hf
  refine MemLp.ae_eq ?_ (hcenter.add (memLp_const (σ 0)))
  filter_upwards [] with x
  change (σ (f x) - σ 0) + σ 0 = σ (f x)
  exact sub_add_cancel _ _

/-- Example 2.1: a globally Lipschitz activation preserves L² in each layer. -/
theorem FourierLayer.memLp_eval {d input output : ℕ} (L : FourierLayer d input output)
    {σ : ℝ → ℝ} {K : NNReal} (hσ : LipschitzWith K σ)
    {h : PeriodicCell d → Channels input} (hh : MemLp h 2 (cellMeasure d)) :
    MemLp (L.eval σ h) 2 (cellMeasure d) := by
  apply memLp_piLp_iff.mpr
  intro i
  change MemLp (fun y => σ ((∑ j : Fin input, L.localWeight i j * h y j) +
    (L.fourierPart h y i).re + L.bias i)) 2 (cellMeasure d)
  have hlocal : MemLp (fun y => ∑ j : Fin input, L.localWeight i j * h y j)
      2 (cellMeasure d) :=
    memLp_finsetSum Finset.univ (fun j _ => (hh.eval_piLp j).const_mul (L.localWeight i j))
  have hcontinuous : Continuous (fun y => (L.fourierPart h y i).re) := by
    apply Complex.continuous_re.comp
    unfold FourierLayer.fourierPart
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (UnitAddTorus.mFourier k).continuous)
  have hfourier : MemLp (fun y => (L.fourierPart h y i).re) 2 (cellMeasure d) :=
    hcontinuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact activation_comp_memLp hσ ((hlocal.add hfourier).add (memLp_const (L.bias i)))

/-- Example 2.1: every finite chain preserves L² for a globally Lipschitz activation. -/
theorem FourierChain.memLp_eval {d input output : ℕ} (L : FourierChain d input output)
    {σ : ℝ → ℝ} {K : NNReal} (hσ : LipschitzWith K σ)
    {h : PeriodicCell d → Channels input} (hh : MemLp h 2 (cellMeasure d)) :
    MemLp (L.eval σ h) 2 (cellMeasure d) := by
  induction L with
  | nil width => exact hh
  | cons L rest ih => exact ih (L.memLp_eval hσ hh)

end KVApproximation.NeuralOperators
