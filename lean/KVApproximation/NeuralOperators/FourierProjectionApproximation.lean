module

public import KVApproximation.NeuralOperators.FourierMapping
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Approximation of averaging kernels by finite Fourier projections

L² convergence of the scalar kernel controls its pairing with every channel
field. Real kernels give conjugate-symmetric projection matrices.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate
open KVApproximation.Analysis

namespace KVApproximation.NeuralOperators

/-- Remark 4.3, retained modes: the rectangular frequency set is symmetric. -/
private theorem neg_mem_frequencyBox {d : ℕ} (cutoff : Fin d → ℕ)
    {k : Fin d → ℤ} (hk : k ∈ frequencyBox cutoff) : -k ∈ frequencyBox cutoff := by
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply] at *
  intro j
  have hj := hk j
  omega

/-- Remark 4.3, finite support: a rectangle contains any prescribed finite
set of frequencies, including the empty set and the zero-dimensional cell. -/
private theorem exists_frequencyBox_superset {d : ℕ} (s : Finset (Fin d → ℤ)) :
    ∃ cutoff : Fin d → ℕ, s ⊆ frequencyBox cutoff := by
  classical
  let cutoff (j : Fin d) := s.sup (fun k => (k j).natAbs)
  refine ⟨cutoff, fun k hk => ?_⟩
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro j
  have hj : (k j).natAbs ≤ cutoff j :=
    Finset.le_sup (f := fun l : Fin d → ℤ => (l j).natAbs) hk
  have hj' : |k j| ≤ (cutoff j : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).2 hj
  exact abs_le.mp hj'

/-- Remark 4.3, Fourier pairing: complexify one real channel coordinate. -/
private def complexCoordinate {n : ℕ} (i : Fin n) : Channels n →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)

/-- Remark 4.3, Fourier pairing: the Hilbert coefficient has the same
negative-frequency convention as the architecture. -/
private theorem coordinate_inner {d n : ℕ} (h : ChannelField d n)
    (k : Fin d → ℤ) (i : Fin n) :
    ⟪UnitAddTorus.mFourierLp 2 k,
      (complexCoordinate i).compLpL 2 (cellMeasure d) h⟫_ℂ = channelFourier h k i := by
  calc
    _ = ⟪UnitAddTorus.mFourierBasis k,
        (complexCoordinate i).compLpL 2 (cellMeasure d) h⟫_ℂ :=
      congrArg (fun q : Lp ℂ 2 (cellMeasure d) =>
        ⟪q, (complexCoordinate i).compLpL 2 (cellMeasure d) h⟫_ℂ)
        (congrFun (UnitAddTorus.coe_mFourierBasis (d := Fin d)) k).symm
    _ = UnitAddTorus.mFourierBasis.repr
        ((complexCoordinate i).compLpL 2 (cellMeasure d) h) k :=
      (UnitAddTorus.mFourierBasis.repr_apply_apply
        ((complexCoordinate i).compLpL 2 (cellMeasure d) h) k).symm
    _ = UnitAddTorus.mFourierCoeff
        ((complexCoordinate i).compLpL 2 (cellMeasure d) h) k :=
      UnitAddTorus.mFourierBasis_repr
        ((complexCoordinate i).compLpL 2 (cellMeasure d) h) k
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(complexCoordinate i).coeFn_compLpL h] with y hy
      change UnitAddTorus.mFourier (-k) y *
        ((complexCoordinate i).compLpL 2 (cellMeasure d) h) y = _
      rw [hy]
      rfl

/-- Remark 4.3, averaging: the real part of a complex L² kernel pairs
continuously with the actual Euclidean L² channel field. -/
private def realPairing {d n : ℕ} :
    Lp ℂ 2 (cellMeasure d) →L[ℝ] ChannelField d n →L[ℝ] Channels n :=
  (Complex.reCLM.smulRight (ContinuousLinearMap.id ℝ (Channels n))).lpPairing
    (cellMeasure d) 2 2

/-- Remark 4.3, averaging: the continuous bilinear pairing is the Bochner integral. -/
private theorem realPairing_eq_integral {d n : ℕ}
    (q : Lp ℂ 2 (cellMeasure d)) (h : ChannelField d n) :
    realPairing q h = ∫ y, (q y).re • h y ∂cellMeasure d :=
  (Complex.reCLM.smulRight (ContinuousLinearMap.id ℝ (Channels n))).lpPairing_eq_integral q h

/-- Remark 4.3, Fourier observation: each coordinate of the real pairing is
the real part of the complex L² inner product. -/
private theorem realPairing_apply {d n : ℕ}
    (q : Lp ℂ 2 (cellMeasure d)) (h : ChannelField d n) (i : Fin n) :
    (realPairing q h) i =
      (⟪q, (complexCoordinate i).compLpL 2 (cellMeasure d) h⟫_ℂ).re := by
  let B := Complex.reCLM.smulRight (ContinuousLinearMap.id ℝ (Channels n))
  let C := complexCoordinate i
  let H := C.compLpL 2 (cellMeasure d) h
  let π := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i
  have hint : Integrable (fun y => (q y).re • h y) (cellMeasure d) :=
    memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 (Lp.memLp q) (Lp.memLp h))
  have hinner : Integrable (fun y => ⟪q y, H y⟫_ℂ) (cellMeasure d) :=
    L2.integrable_inner q H
  calc
    (realPairing q h) i = π (∫ y, (q y).re • h y ∂cellMeasure d) :=
      congrArg (fun v : Channels n => v i) (realPairing_eq_integral q h)
    _ = ∫ y, π ((q y).re • h y) ∂cellMeasure d :=
      (π.integral_comp_comm hint).symm
    _ = ∫ y, Complex.reCLM ⟪q y, H y⟫_ℂ ∂cellMeasure d := by
      apply integral_congr_ae
      filter_upwards [C.coeFn_compLpL h] with y hy
      change (q y).re * h y i = (⟪q y, C.compLpL 2 (cellMeasure d) h y⟫_ℂ).re
      rw [hy]
      simp [C, complexCoordinate, RCLike.inner_apply, mul_comm]
    _ = Complex.reCLM (∫ y, ⟪q y, H y⟫_ℂ ∂cellMeasure d) :=
      Complex.reCLM.integral_comp_comm hinner
    _ = (⟪q, H⟫_ℂ).re := congrArg Complex.re (L2.inner_def q H).symm

/-- Remark 4.3, finite Fourier observation: a real L² averaging kernel can
be approximated in operator norm by an actual conjugate-symmetric projection. -/
theorem exists_fourierProjection_approx_integral
    {d n : ℕ} (κ : Lp ℝ 2 (cellMeasure d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : FourierProjection d n n, ∀ h : ChannelField d n,
      ‖P.eval h - ∫ y, κ y • h y ∂cellMeasure d‖ ≤ ε * ‖h‖ := by
  classical
  let K : Lp ℂ 2 (cellMeasure d) := Complex.ofRealCLM.compLpL 2 (cellMeasure d) κ
  let a (k : Fin d → ℤ) : ℂ := UnitAddTorus.mFourierCoeff K k
  have ha (k : Fin d → ℤ) :
      a k = ∫ y, UnitAddTorus.mFourier (-k) y * (κ y : ℂ) ∂cellMeasure d := by
    apply integral_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL κ] with y hy
    change UnitAddTorus.mFourier (-k) y *
      (Complex.ofRealCLM.compLpL 2 (cellMeasure d) κ) y = _
    rw [hy]
    rfl
  have hasym (k : Fin d → ℤ) : a (-k) = star (a k) := by
    rw [ha, ha]
    change (∫ y, UnitAddTorus.mFourier (- -k) y * (κ y : ℂ) ∂cellMeasure d) =
      conj (∫ y, UnitAddTorus.mFourier (-k) y * (κ y : ℂ) ∂cellMeasure d)
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [UnitAddTorus.mFourier_neg]
  let R : Lp ℂ 2 (cellMeasure d) →L[ℝ] ChannelField d n →L[ℝ] Channels n := realPairing
  let δ := ε / (‖R‖ + 1)
  have hden : 0 < ‖R‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hsum : Tendsto (fun s : Finset (Fin d → ℤ) =>
      ∑ k ∈ s, a k • UnitAddTorus.mFourierLp 2 k) atTop (𝓝 K) :=
    UnitAddTorus.hasSum_mFourier_series_L2 K
  obtain ⟨s, hs⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hsum) δ hδ)
  obtain ⟨cutoff, hcutoff⟩ := exists_frequencyBox_superset s
  let q : Lp ℂ 2 (cellMeasure d) :=
    ∑ k ∈ frequencyBox cutoff, a k • UnitAddTorus.mFourierLp 2 k
  have hq : ‖q - K‖ < δ := by
    have hd : dist q K < δ := hs (frequencyBox cutoff) hcutoff
    exact (dist_eq_norm q K) ▸ hd
  let w (k : Fin d → ℤ) : Matrix (Fin n) (Fin n) ℂ :=
    if k ∈ frequencyBox cutoff then fun i j => if j = i then star (a k) else 0 else 0
  have hw (k : Fin d → ℤ) : w k ≠ 0 → k ∈ frequencyBox cutoff := by
    intro hk
    by_contra hnot
    exact hk (by simp [w, hnot])
  let multiplier := Finsupp.onFinset (frequencyBox cutoff) w hw
  let P : FourierProjection d n n := {
    cutoff := cutoff
    multiplier := multiplier
    support_subset := Finsupp.support_onFinset_subset
    conjugate_symmetry := by
      intro k i j
      change w (-k) i j = star (w k i j)
      by_cases hk : k ∈ frequencyBox cutoff
      · have hneg := neg_mem_frequencyBox cutoff hk
        by_cases hji : j = i <;> simp [w, hk, hneg, hasym, hji]
      · have hneg : -k ∉ frequencyBox cutoff := by
          intro h
          exact hk (by simpa only [neg_neg] using neg_mem_frequencyBox cutoff h)
        simp [w, hk, hneg] }
  have hP (h : ChannelField d n) : P.eval h = R q h := by
    apply PiLp.ext
    intro i
    change (P.eval h) i = (realPairing q h) i
    rw [realPairing_apply]
    change (∑ k ∈ frequencyBox cutoff, ∑ j : Fin n,
      P.multiplier k i j * channelFourier h k j).re = _
    apply congrArg Complex.re
    change (∑ k ∈ frequencyBox cutoff, ∑ j : Fin n,
      w k i j * channelFourier h k j) =
        ⟪∑ k ∈ frequencyBox cutoff, a k • UnitAddTorus.mFourierLp 2 k,
          (complexCoordinate i).compLpL 2 (cellMeasure d) h⟫_ℂ
    calc
      _ = ∑ k ∈ frequencyBox cutoff, star (a k) * channelFourier h k i := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [w, hk, ite_mul]
      _ = _ := by
        symm
        refine (sum_inner (𝕜 := ℂ) (E := Lp ℂ 2 (cellMeasure d))
          (frequencyBox cutoff) (fun k => a k • UnitAddTorus.mFourierLp 2 k)
          ((complexCoordinate i).compLpL 2 (cellMeasure d) h)).trans ?_
        apply Finset.sum_congr rfl
        intro k hk
        exact (inner_smul_left (𝕜 := ℂ) (E := Lp ℂ 2 (cellMeasure d))
          (UnitAddTorus.mFourierLp 2 k)
          ((complexCoordinate i).compLpL 2 (cellMeasure d) h) (a k)).trans
          (congrArg (fun z : ℂ => star (a k) * z) (coordinate_inner h k i))
  have hK (h : ChannelField d n) : R K h = ∫ y, κ y • h y ∂cellMeasure d := by
    change realPairing K h = _
    rw [realPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL κ] with y hy
    change ((Complex.ofRealCLM.compLpL 2 (cellMeasure d) κ) y).re • h y = _
    rw [hy]
    rfl
  have hRδ : ‖R‖ * δ ≤ ε := calc
    ‖R‖ * δ ≤ (‖R‖ + 1) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ = ε := mul_div_cancel₀ ε hden.ne'
  refine ⟨P, fun h => ?_⟩
  calc
    ‖P.eval h - ∫ y, κ y • h y ∂cellMeasure d‖ = ‖R (q - K) h‖ := by
      rw [hP, ← hK, map_sub, sub_apply]
    _ ≤ ‖R‖ * ‖q - K‖ * ‖h‖ := R.le_opNorm₂ (q - K) h
    _ ≤ (‖R‖ * δ) * ‖h‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hq.le (norm_nonneg R)) (norm_nonneg h)
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hRδ (norm_nonneg h)

end KVApproximation.NeuralOperators
