module

public import KVApproximation.NeuralOperators.FourierMapping
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Reality of conjugate-symmetric Fourier mappings
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Example 2.1, retained modes: the rectangular frequency set is invariant
under sign reversal, including the zero mode and zero-dimensional cell. -/
private theorem neg_mem_frequencyBox {d : ℕ} (cutoff : Fin d → ℕ)
    {k : Fin d → ℤ} (hk : k ∈ frequencyBox cutoff) : -k ∈ frequencyBox cutoff := by
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply] at *
  intro j
  have hj := hk j
  omega

/-- Example 2.1, Fourier coefficients: a real channel field has conjugate
coefficients at opposite frequencies. -/
private theorem channelFourier_neg {d n : ℕ} (h : PeriodicCell d → Channels n)
    (k : Fin d → ℤ) (j : Fin n) : channelFourier h (-k) j = star (channelFourier h k j) := by
  unfold channelFourier
  change (∫ y, UnitAddTorus.mFourier (- -k) y * (h y j : ℂ) ∂cellMeasure d) =
    conj (∫ y, UnitAddTorus.mFourier (-k) y * (h y j : ℂ) ∂cellMeasure d)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [UnitAddTorus.mFourier_neg]

/-- Example 2.1, conjugate pairing: reindexing the retained modes by sign
reversal makes a conjugate-symmetric sum real. -/
private theorem im_sum_frequencyBox_eq_zero {d : ℕ} (cutoff : Fin d → ℕ)
    (q : (Fin d → ℤ) → ℂ) (hq : ∀ k, q (-k) = star (q k)) :
    (∑ k ∈ frequencyBox cutoff, q k).im = 0 := by
  classical
  have heq : ∑ k ∈ frequencyBox cutoff, q k =
      ∑ k ∈ frequencyBox cutoff, star (q k) := by
    refine Finset.sum_bij (fun k _ => -k)
      (fun k hk => neg_mem_frequencyBox cutoff hk)
      (fun k _ l _ hkl => neg_injective hkl)
      (fun k hk => ⟨-k, neg_mem_frequencyBox cutoff hk, neg_neg k⟩) ?_
    intro k hk
    rw [hq, star_star]
  have hconj : conj (∑ k ∈ frequencyBox cutoff, q k) =
      ∑ k ∈ frequencyBox cutoff, q k := by
    rw [map_sum]
    exact heq.symm
  have him : -(∑ k ∈ frequencyBox cutoff, q k).im =
      (∑ k ∈ frequencyBox cutoff, q k).im := congrArg Complex.im hconj
  linarith

/-- Example 2.1: conjugate symmetry of the retained modes and matrices
makes the Fourier layer real-valued on real L² fields. -/
theorem FourierLayer.fourierPart_im {d input output : ℕ} (L : FourierLayer d input output)
    (h : PeriodicCell d → Channels input) (hh : MemLp h 2 (cellMeasure d))
    (y : PeriodicCell d) (i : Fin output) : (L.fourierPart h y i).im = 0 := by
  unfold FourierLayer.fourierPart
  apply im_sum_frequencyBox_eq_zero
  intro k
  change (∑ j : Fin input, L.multiplier (-k) i j * channelFourier h (-k) j) *
      UnitAddTorus.mFourier (-k) y =
    (starRingEnd ℂ) ((∑ j : Fin input, L.multiplier k i j * channelFourier h k j) *
      UnitAddTorus.mFourier k y)
  rw [map_mul, map_sum]
  simp only [L.conjugate_symmetry, channelFourier_neg, UnitAddTorus.mFourier_neg,
    map_mul, starRingEnd_apply]

/-- Example 2.1: the conjugate-symmetric Fourier projection is real-valued. -/
theorem FourierProjection.complexValue_im {d input output : ℕ}
    (P : FourierProjection d input output) (h : PeriodicCell d → Channels input)
    (hh : MemLp h 2 (cellMeasure d)) (i : Fin output) :
    (P.complexValue h i).im = 0 := by
  unfold FourierProjection.complexValue
  apply im_sum_frequencyBox_eq_zero
  intro k
  change (∑ j : Fin input, P.multiplier (-k) i j * channelFourier h (-k) j) =
    (starRingEnd ℂ) (∑ j : Fin input, P.multiplier k i j * channelFourier h k j)
  rw [map_sum]
  simp only [P.conjugate_symmetry, channelFourier_neg, map_mul, starRingEnd_apply]

end KVApproximation.NeuralOperators
