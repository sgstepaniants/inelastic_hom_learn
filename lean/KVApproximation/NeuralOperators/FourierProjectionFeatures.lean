module

public import KVApproximation.NeuralOperators.FourierMapping
public import KVApproximation.Analysis.PeriodicFourierFunctionals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Scalar Fourier projections as separating features

Paired weights at opposite frequencies recover real and imaginary Fourier
coefficients, including the coinciding pair at frequency zero.
-/

public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, retained modes: a rectangular frequency set is symmetric. -/
private theorem neg_mem_frequencyBox {d : ℕ} (cutoff : Fin d → ℕ)
    {k : Fin d → ℤ} (hk : k ∈ frequencyBox cutoff) : -k ∈ frequencyBox cutoff := by
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply] at *
  intro j
  have hj := hk j
  omega

/-- Remark 4.3, real inputs: opposite Fourier coefficients are conjugates. -/
private theorem channelFourier_neg {d n : ℕ} (h : PeriodicCell d → Channels n)
    (k : Fin d → ℤ) (j : Fin n) : channelFourier h (-k) j = star (channelFourier h k j) := by
  unfold channelFourier
  change (∫ y, UnitAddTorus.mFourier (- -k) y * (h y j : ℂ) ∂cellMeasure d) =
    conj (∫ y, UnitAddTorus.mFourier (-k) y * (h y j : ℂ) ∂cellMeasure d)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [UnitAddTorus.mFourier_neg]

/-- Remark 4.3, Fourier features: paired opposite-frequency weights realize
the real part of any complex multiple of a single channel coefficient. -/
theorem exists_scalarFourierProjection {d n : ℕ}
    (k : Fin d → ℤ) (j : Fin n) (z : ℂ) :
    ∃ P : FourierProjection d n 1, ∀ h : ChannelField d n,
      P.eval h 0 = (z * channelFourier h k j).re := by
  classical
  let cutoff (i : Fin d) := (k i).natAbs
  have hk : k ∈ frequencyBox cutoff := by
    simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    change -((k i).natAbs : ℤ) ≤ k i ∧ k i ≤ ((k i).natAbs : ℤ)
    simpa only [Int.natCast_natAbs] using (abs_le.mp (le_refl |k i|))
  have hnegk := neg_mem_frequencyBox cutoff hk
  let W (l : Fin d → ℤ) : Matrix (Fin 1) (Fin n) ℂ := fun _ t =>
    if t = j then (if l = k then z / 2 else 0) +
      (if l = -k then conj (z / 2) else 0) else 0
  have hW (l : Fin d → ℤ) : W l ≠ 0 → l ∈ frequencyBox cutoff := by
    intro hnonzero
    by_contra hl
    have hlk : l ≠ k := fun h => hl (h.symm ▸ hk)
    have hlneg : l ≠ -k := fun h => hl (h.symm ▸ hnegk)
    exact hnonzero (by ext i t; simp [W, hlk, hlneg])
  let multiplier := Finsupp.onFinset (frequencyBox cutoff) W hW
  let P : FourierProjection d n 1 := {
    cutoff := cutoff
    multiplier := multiplier
    support_subset := Finsupp.support_onFinset_subset
    conjugate_symmetry := by
      intro l i t
      change W (-l) i t = conj (W l i t)
      have hneg : -l = k ↔ l = -k := by
        constructor <;> intro h <;> simpa only [neg_neg] using congrArg Neg.neg h
      by_cases ht : t = j
      · simp only [W, ite_eq_left ht, hneg, neg_inj]
        split_ifs <;> simp [map_add, add_comm]
      · simp [W, ht] }
  have hcomplex (h : ChannelField d n) : P.complexValue h 0 =
      (z / 2) * channelFourier h k j + conj (z / 2) * channelFourier h (-k) j := by
    have hrow (l : Fin d → ℤ) :
        (∑ t : Fin n, W l 0 t * channelFourier h l t) =
          ((if l = k then z / 2 else 0) + (if l = -k then conj (z / 2) else 0)) *
            channelFourier h l j := by
      simp [W, ite_mul]
    calc
      _ = ∑ l ∈ frequencyBox cutoff,
          ((if l = k then z / 2 else 0) + (if l = -k then conj (z / 2) else 0)) *
            channelFourier h l j := by
        change (∑ l ∈ frequencyBox cutoff, ∑ t : Fin n,
          W l 0 t * channelFourier h l t) = _
        exact Finset.sum_congr rfl (fun l hl => hrow l)
      _ = _ := by
        simp [add_mul, ite_mul, Finset.sum_add_distrib, hk, hnegk]
  refine ⟨P, fun h => ?_⟩
  change (P.complexValue h 0).re = _
  rw [hcomplex, channelFourier_neg]
  change ((z / 2) * channelFourier h k j +
    conj (z / 2) * conj (channelFourier h k j)).re = _
  have hpair : conj (z / 2) * conj (channelFourier h k j) =
      conj ((z / 2) * channelFourier h k j) :=
    (map_mul (starRingEnd ℂ) (z / 2) (channelFourier h k j)).symm
  rw [hpair]
  calc
    _ = ((z / 2) * channelFourier h k j + (z / 2) * channelFourier h k j).re := by
      simp only [Complex.add_re, Complex.conj_re]
    _ = (z * channelFourier h k j).re := congrArg Complex.re (by ring)

/-- Remark 4.3, separation: all scalar projections in the actual finite
conjugate-symmetric architecture determine the L² channel field. -/
theorem eq_of_scalarFourierProjections_eq {d n : ℕ} {h g : ChannelField d n}
    (heq : ∀ P : FourierProjection d n 1, P.eval h 0 = P.eval g 0) : h = g := by
  apply euclideanL2_eq_of_fourier_integrals_eq
  intro k j
  change channelFourier h k j = channelFourier g k j
  have hz (z : ℂ) :
      (z * channelFourier h k j).re = (z * channelFourier g k j).re := by
    obtain ⟨P, hP⟩ := exists_scalarFourierProjection k j z
    exact (hP h).symm.trans ((heq P).trans (hP g))
  apply Complex.ext
  · simpa only [one_mul] using hz 1
  · simpa [Complex.mul_re] using hz (-Complex.I)

end KVApproximation.NeuralOperators
