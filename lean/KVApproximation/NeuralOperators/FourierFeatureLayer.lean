module

public import KVApproximation.NeuralOperators.FourierMapping
public import KVApproximation.Analysis.PeriodicFourierFunctionals

/-!
# Finite observations realized by a Fourier layer
-/

public section

noncomputable section

open KVApproximation.Analysis
open scoped ComplexConjugate

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, finite support: enlarging each coordinate cutoff enlarges
the rectangular frequency set. -/
private theorem frequencyBox_mono {d : ℕ} {a b : Fin d → ℕ}
    (hab : ∀ j, a j ≤ b j) : frequencyBox a ⊆ frequencyBox b := by
  intro k hk
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc] at hk ⊢
  intro j
  have hj : (a j : ℤ) ≤ (b j : ℤ) := Nat.cast_le.mpr (hab j)
  exact ⟨(neg_le_neg hj).trans (hk j).1, (hk j).2.trans hj⟩

/-- Remark 4.3, zero padding: coefficients outside the prescribed
rectangle vanish as matrices. -/
private theorem projection_multiplier_zero {d input output : ℕ}
    (P : FourierProjection d input output) {k : Fin d → ℤ}
    (hk : k ∉ frequencyBox P.cutoff) : P.multiplier k = 0 :=
  Finsupp.notMem_support_iff.mp (fun h => hk (P.support_subset h))

/-- Remark 4.3, finite-feature realization: one actual Fourier layer with
zero local matrix and constant bias realizes every finite real linear
combination of scalar Fourier observations at the spatial origin. -/
theorem exists_fourier_feature_layer {d input features output : ℕ}
    (P : Fin features → FourierProjection d input 1)
    (w : Matrix (Fin output) (Fin features) ℝ) (b : Fin output → ℝ) :
    ∃ L : FourierLayer d input output,
      L.localWeight = 0 ∧ L.bias = b ∧
        ∀ (h : PeriodicCell d → Channels input) (j : Fin output),
          (L.fourierPart h 0 j).re = ∑ i : Fin features, w j i * (P i).eval h 0 := by
  classical
  let cutoff (j : Fin d) := Finset.univ.sup (fun i : Fin features => (P i).cutoff j)
  have hsub (i : Fin features) : frequencyBox (P i).cutoff ⊆ frequencyBox cutoff :=
    frequencyBox_mono (fun j => Finset.le_sup
      (f := fun t : Fin features => (P t).cutoff j) (Finset.mem_univ i))
  let W (k : Fin d → ℤ) : Matrix (Fin output) (Fin input) ℂ :=
    fun j t => ∑ i : Fin features, (w j i : ℂ) * (P i).multiplier k 0 t
  have hW (k : Fin d → ℤ) : W k ≠ 0 → k ∈ frequencyBox cutoff := by
    intro hnonzero
    by_contra hk
    have hzero (i : Fin features) : (P i).multiplier k = 0 :=
      projection_multiplier_zero (P i) (fun hi => hk (hsub i hi))
    apply hnonzero
    ext j t
    simp [W, hzero]
  let multiplier := Finsupp.onFinset (frequencyBox cutoff) W hW
  let L : FourierLayer d input output := {
    localWeight := 0
    bias := b
    cutoff := cutoff
    multiplier := multiplier
    support_subset := Finsupp.support_onFinset_subset
    conjugate_symmetry := by
      intro k j t
      change (∑ i : Fin features, (w j i : ℂ) * (P i).multiplier (-k) 0 t) =
        conj (∑ i : Fin features, (w j i : ℂ) * (P i).multiplier k 0 t)
      simp only [map_sum, map_mul, FourierProjection.conjugate_symmetry, starRingEnd_apply]
      apply Finset.sum_congr rfl
      intro i hi
      have hw : star (w j i : ℂ) = (w j i : ℂ) := Complex.conj_ofReal (w j i)
      exact congrArg (fun z : ℂ => z * star ((P i).multiplier k 0 t)) hw.symm }
  have hext (i : Fin features) (h : PeriodicCell d → Channels input) :
      (∑ k ∈ frequencyBox cutoff, ∑ t : Fin input,
        (P i).multiplier k 0 t * channelFourier h k t) = (P i).complexValue h 0 := by
    symm
    apply Finset.sum_subset (hsub i)
    intro k hk hki
    have hzero := projection_multiplier_zero (P i) hki
    simp [hzero]
  have horigin (k : Fin d → ℤ) : UnitAddTorus.mFourier k (0 : PeriodicCell d) = 1 := by
    simp [UnitAddTorus.mFourier, fourier_eval_zero]
  have hcomplex (h : PeriodicCell d → Channels input) (j : Fin output) :
      L.fourierPart h 0 j =
        ∑ i : Fin features, (w j i : ℂ) * (P i).complexValue h 0 := by
    change (∑ k ∈ frequencyBox cutoff,
      (∑ t : Fin input, (∑ i : Fin features,
        (w j i : ℂ) * (P i).multiplier k 0 t) * channelFourier h k t) *
          UnitAddTorus.mFourier k 0) = _
    simp only [horigin, mul_one]
    calc
      _ = ∑ i : Fin features, (w j i : ℂ) *
          (∑ k ∈ frequencyBox cutoff, ∑ t : Fin input,
            (P i).multiplier k 0 t * channelFourier h k t) := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact (Finset.sum_congr rfl (fun k hk => Finset.sum_comm)).trans Finset.sum_comm
      _ = _ := by simp only [hext]
  refine ⟨L, rfl, rfl, fun h j => ?_⟩
  rw [hcomplex]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rfl

/-- Remark 4.3, continuous hidden fields: with zero local matrix, a finite
Fourier layer is jointly continuous in its L² input and spatial point for
every continuous activation. -/
theorem FourierLayer.continuous_eval_of_zero_localWeight {d input output : ℕ}
    (L : FourierLayer d input output) (hL : L.localWeight = 0)
    {σ : ℝ → ℝ} (hσ : Continuous σ) :
    Continuous (fun p : ChannelField d input × PeriodicCell d => L.eval σ p.1 p.2) := by
  have hc (k : Fin d → ℤ) (j : Fin input) :
      Continuous (fun p : ChannelField d input × PeriodicCell d =>
        channelFourier p.1 k j) := by
    obtain ⟨A, hA⟩ := exists_periodicFourierCoefficientCLM k j
    exact (A.continuous.comp continuous_fst).congr (fun p => hA p.1)
  have hf (j : Fin output) :
      Continuous (fun p : ChannelField d input × PeriodicCell d =>
        L.fourierPart p.1 p.2 j) := by
    unfold FourierLayer.fourierPart
    apply continuous_finsetSum
    intro k hk
    exact (continuous_finsetSum _ (fun t ht => continuous_const.mul (hc k t))).mul
      ((UnitAddTorus.mFourier k).continuous.comp continuous_snd)
  have heval : (fun p : ChannelField d input × PeriodicCell d => L.eval σ p.1 p.2) =
      fun p => WithLp.toLp 2 (fun j => σ ((L.fourierPart p.1 p.2 j).re + L.bias j)) := by
    funext p
    simp [FourierLayer.eval, hL]
  rw [heval]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin output => ℝ)).comp
    (continuous_pi fun j => hσ.comp ((Complex.continuous_re.comp (hf j)).add continuous_const))

end KVApproximation.NeuralOperators
