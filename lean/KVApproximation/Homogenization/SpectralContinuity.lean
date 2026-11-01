module

public import KVApproximation.Homogenization.CellSpectralMeasure
public import KVApproximation.Homogenization.CellConvergence
public import KVApproximation.Homogenization.ConstantStrainIdentities
public import KVApproximation.OperatorTheory.StrongConvergence
public import KVApproximation.Spectral.CompressionApproximation
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Weak continuity of the cell spectral measure

Lemma B.5 approximates continuous tests by polynomials. Their moments are
pairings of relaxation powers and mismatch, on the original corrector space.
The functional-calculus remainder bound is uniform in the material.
-/

public section

open MeasureTheory Filter
open scoped Topology InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.Homogenization
open KVApproximation.OperatorTheory

namespace KVApproximation.Spectral

/-- Lemma B.5: linearity of the continuous test pairing. -/
private theorem test_pairing_add {d : ℕ} (ν : TensorMeasure d)
    (f g : ℝ → ℝ) (hf : Integrable f ν.variation) (hg : Integrable g ν.variation)
    (e k : Symmetric d) :
    ⟪e, action (tensorIntegral ν (fun r => f r + g r)) k⟫_ℝ =
      ⟪e, action (tensorIntegral ν f) k⟫_ℝ + ⟪e, action (tensorIntegral ν g) k⟫_ℝ := by
  let φ : Elasticity d →L[ℝ] ℝ := (innerSL ℝ e).comp ((actionL d).flip k)
  change φ (VectorMeasure.integral ν (fun r => f r + g r) _) =
    φ (VectorMeasure.integral ν f _) + φ (VectorMeasure.integral ν g _)
  rw [VectorMeasure.integral_fun_add hf hg, map_add]

/-- Lemma B.5: scalar multiplication of a monomial test. -/
private theorem test_pairing_mul {d : ℕ} (ν : TensorMeasure d)
    (f : ℝ → ℝ) (c : ℝ) (e k : Symmetric d) :
    ⟪e, action (tensorIntegral ν (fun r => c * f r)) k⟫_ℝ =
      c * ⟪e, action (tensorIntegral ν f) k⟫_ℝ := by
  let φ : Elasticity d →L[ℝ] ℝ := (innerSL ℝ e).comp ((actionL d).flip k)
  change φ (VectorMeasure.integral ν (fun r => c • f r) _) =
    c • φ (VectorMeasure.integral ν f _)
  rw [VectorMeasure.integral_fun_smul, map_smul]

section Polynomial

variable {d : ℕ} {αV βV αE βE : ℝ}
variable (V E : CoerciveField d) (Vseq Eseq : ℕ → CoerciveField d)
variable (hαV : 0 < αV) (hβV : 0 < βV) (hαE : 0 < αE) (hβE : 0 < βE)
variable (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field)
variable (hVseq : ∀ n, HasFieldBounds αV βV (Vseq n).field)
variable (hEseq : ∀ n, HasFieldBounds αE βE (Eseq n).field)
variable (hVconv : Tendsto
  (fun n => eLpNorm (fun y => (Vseq n).field y - V.field y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (hEconv : Tendsto
  (fun n => eLpNorm (fun y => (Eseq n).field y - E.field y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (ν : TensorMeasure d) (νseq : ℕ → TensorMeasure d)
variable (hc : IsCompressedMeasure V.toForm E.toForm (correctorSubspace d) (constantStrainL d) ν)
variable (hcseq : ∀ n, IsCompressedMeasure (Vseq n).toForm (Eseq n).toForm
  (correctorSubspace d) (constantStrainL d) (νseq n))

include hαV hβV hαE hβE hV hE hVseq hEseq hVconv hEconv hc hcseq

set_option maxHeartbeats 400000 in
/-- Lemma B.5: convergence of each monomial pairing, including the changing
viscous inner product and the moving mismatch vectors. -/
private theorem cell_moment_tendsto (j : ℕ) (e g : Symmetric d) :
    Tendsto (fun n => ⟪e, action (tensorIntegral (νseq n) (fun r => r ^ j)) g⟫_ℝ)
      atTop (𝓝 ⟪e, action (tensorIntegral ν (fun r => r ^ j)) g⟫_ℝ) := by
  let : NormedAddCommGroup (correctorSubspace d) :=
    inferInstanceAs (NormedAddCommGroup (correctorSubspace d).toSubmodule)
  let : NormedSpace ℝ (correctorSubspace d) :=
    inferInstanceAs (NormedSpace ℝ (correctorSubspace d).toSubmodule)
  have hV' : V.toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hV u
  have hE' : E.toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hE u
  have hVs (n) : (Vseq n).toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hVseq n u
  have hEs (n) : (Eseq n).toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hEseq n u
  simp only [compressedMeasure_moment V.toForm E.toForm (correctorSubspace d)
    (constantStrainL d) ν hc hαV hβV hαE hβE hV' hE' j e g,
    compressedMeasure_moment (Vseq _).toForm (Eseq _).toForm (correctorSubspace d)
    (constantStrainL d) (νseq _) (hcseq _) hαV hβV hαE hβE (hVs _) (hEs _) j e g]
  have hcell := cell_operators_converge V E Vseq Eseq hαV hβV hαE hβE
    hV hE hVseq hEseq hVconv hEconv
  have hnorm (n : ℕ) : ‖cellRelaxation (Vseq n) (Eseq n)‖ ≤ βE / αV :=
    relaxation_opNorm_le (Vseq n).toForm (Eseq n).toForm (correctorSubspace d)
      hαV hβE.le (fun u => (hVs n u).1) (fun u => (hEs n u).2)
  have hpower (n : ℕ) : ‖cellRelaxation (Vseq n) (Eseq n) ^ j‖ ≤ (βE / αV) ^ j := by
    by_cases hj : j = 0
    · subst j
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro u
      simp only [pow_zero, one_apply_eq_self, one_mul, le_refl]
    · exact (norm_pow_le' _ (Nat.pos_of_ne_zero hj)).trans
        (pow_le_pow_left₀ (norm_nonneg _) (hnorm n) j)
  have hφ := tendsto_apply_of_uniform_bound
    (cellRelaxation V E ^ j) (fun n => cellRelaxation (Vseq n) (Eseq n) ^ j)
      hpower (hcell.2.2.2.2 j) (hcell.2.2.1 (constantStrainL d e))
  have hψ := hcell.2.2.1 (constantStrainL d g)
  have hφH := (continuous_subtype_val.tendsto _).comp hφ
  have hψH := (continuous_subtype_val.tendsto _).comp hψ
  have hA (u : StrainField d) :
      Tendsto (fun n => (Vseq n).toForm.riesz u) atTop (𝓝 (V.toForm.riesz u)) := by
    have h := multiplication_strong_tendsto V.field (fun n => (Vseq n).field)
      (κ := Real.sqrt (strainDimension d) * βV)
      (mul_nonneg (Real.sqrt_nonneg _) hβV.le)
      (fun n => HasFieldBounds.eLpNorm_top_le (Vseq n).field hαV.le hβV.le (hVseq n))
      hVconv u
    have heq (A : CoerciveField d) : A.toForm.riesz u = multiplication A.field u :=
      congrArg (fun L : StrainField d →L[ℝ] StrainField d => L u) A.riesz_eq_multiplication
    simpa only [heq] using h
  have hAnorm (n) : ‖(Vseq n).toForm.riesz.toContinuousLinearMap‖ ≤ βV :=
    CoerciveForm.riesz_opNorm_le _ hβV.le (fun u => (hVs n u).2)
  have hAφ := tendsto_apply_of_uniform_bound V.toForm.riesz.toContinuousLinearMap
    (fun n => (Vseq n).toForm.riesz.toContinuousLinearMap) hAnorm hA hφH
  have hpair := hAφ.inner (𝕜 := ℝ) hψH
  simp only [ContinuousLinearEquiv.coe_coe, CoerciveForm.riesz_spec,
    Function.comp_def] at hpair
  exact hpair

/-- Lemma B.5: finite sums of the convergent monomial pairings give
convergence for each fixed polynomial. -/
private theorem cell_polynomial_tendsto (p : Polynomial ℝ) (e g : Symmetric d) :
    Tendsto (fun n => ⟪e, action (tensorIntegral (νseq n) p.eval) g⟫_ℝ)
      atTop (𝓝 ⟪e, action (tensorIntegral ν p.eval) g⟫_ℝ) := by
  have hV' : V.toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hV u
  have hE' : E.toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hE u
  have hVs (n) : (Vseq n).toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hVseq n u
  have hEs (n) : (Eseq n).toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hEseq n u
  have hi (p : Polynomial ℝ) : Integrable p.eval ν.variation :=
    (compressedMeasure_integral V.toForm E.toForm (correctorSubspace d)
      (constantStrainL d) ν hc hαV hβV hαE hβE hV' hE' p.eval (by fun_prop)).1
  have his (n : ℕ) (p : Polynomial ℝ) : Integrable p.eval (νseq n).variation :=
    (compressedMeasure_integral (Vseq n).toForm (Eseq n).toForm (correctorSubspace d)
      (constantStrainL d) (νseq n) (hcseq n) hαV hβV hαE hβE
        (hVs n) (hEs n) p.eval (by fun_prop)).1
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, test_pairing_add ν _ _ (hi p) (hi q),
      test_pairing_add (νseq _) _ _ (his _ p) (his _ q)]
    exact hp.add hq
  | monomial j c =>
    simp only [Polynomial.eval_monomial, test_pairing_mul]
    exact (cell_moment_tendsto V E Vseq Eseq hαV hβV hαE hβE
      hV hE hVseq hEseq hVconv hEconv ν νseq hc hcseq j e g).const_mul c

end Polynomial

variable {d : ℕ} {αV βV αE βE : ℝ}
variable (V E : CoerciveField d) (Vseq Eseq : ℕ → CoerciveField d)
variable (C : CellConstitutiveModel V E)
variable (Cseq : ∀ n, CellConstitutiveModel (Vseq n) (Eseq n))
variable (hαV : 0 < αV) (hVorder : αV ≤ βV) (hαE : 0 < αE) (hEorder : αE ≤ βE)
variable (hV : HasFieldBounds αV βV V.field) (hE : HasFieldBounds αE βE E.field)
variable (hVseq : ∀ n, HasFieldBounds αV βV (Vseq n).field)
variable (hEseq : ∀ n, HasFieldBounds αE βE (Eseq n).field)
variable (hVconv : Tendsto
  (fun n => eLpNorm (fun y => (Vseq n).field y - V.field y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (hEconv : Tendsto
  (fun n => eLpNorm (fun y => (Eseq n).field y - E.field y) 1 (cellMeasure d)) atTop (𝓝 0))
variable (ν : TensorMeasure d) (νseq : ℕ → TensorMeasure d)
variable (hν : IsSpectralRepresentation ν C.kernel (lowerRate αE βV) (upperRate βE αV))
variable (hνseq : ∀ n, IsSpectralRepresentation (νseq n) (Cseq n).kernel
  (lowerRate αE βV) (upperRate βE αV))

include C Cseq hαV hVorder hαE hEorder hV hE hVseq hEseq hVconv hEconv hν hνseq

/-- Lemma B.5 (`lem:weak_convergence`): integration against every continuous
test on the common interval converges in the finite-dimensional tensor space.
The proof uses polynomial approximation and strong convergence of powers of R.
Integrability makes the totalized vector integrals agree with those in the paper. -/
theorem spectral_measures_converge (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (lowerRate αE βV) (upperRate βE αV))) :
    Integrable f ν.variation ∧ (∀ n, Integrable f (νseq n).variation) ∧
      Tendsto (fun n => tensorIntegral (νseq n) f) atTop (𝓝 (tensorIntegral ν f)) := by
  have hβV := hαV.trans_le hVorder
  have hβE := hαE.trans_le hEorder
  have hc := cell_spectral_measure_isCompressed V E C hαV hβV hαE hβE hV hE ν hν
  have hcseq (n) := cell_spectral_measure_isCompressed (Vseq n) (Eseq n) (Cseq n)
    hαV hβV hαE hβE (hVseq n) (hEseq n) (νseq n) (hνseq n)
  have hV' : V.toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hV u
  have hE' : E.toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hE u
  have hVs (n) : (Vseq n).toForm.HasBounds αV βV := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hVseq n u
  have hEs (n) : (Eseq n).toForm.HasBounds αE βE := by
    intro u
    simpa only [CoerciveField.toForm, boundedFieldForm_apply] using hEseq n u
  refine ⟨ν.integrable_continuousOn hν.2.2.1 hν.2.1 f hf,
    fun n => (νseq n).integrable_continuousOn (hνseq n).2.2.1 (hνseq n).2.1 f hf, ?_⟩
  apply tendsto_of_inner_action
  intro e g
  let J (ρ : TensorMeasure d) (q : ℝ → ℝ) := ⟪e, action (tensorIntegral ρ q) g⟫_ℝ
  let M := (βV * βE / αE) * ‖e‖ * ‖g‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / (3 * (M + 1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) (by positivity))
  have hδM : δ * M < ε / 3 := by
    calc
      δ * M < δ * (M + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
      _ = ε / 3 := by
        dsimp [δ]
        field_simp [(show M + 1 ≠ 0 by positivity)]
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (lowerRate αE βV) (upperRate βE αV) f hf δ hδ
  have hpcont : ContinuousOn p.eval (Set.Icc (αE / βV) (βE / αV)) := by fun_prop
  have happrox : ∀ r ∈ Set.Icc (αE / βV) (βE / αV), |f r - p.eval r| ≤ δ := by
    intro r hr
    simpa only [abs_sub_comm] using (hp r hr).le
  have herr : dist (J ν f) (J ν p.eval) ≤ δ * M := by
    simpa only [J, Real.dist_eq, norm_constantStrain, M, mul_assoc] using
      compressedMeasure_pairing_sub_le V.toForm E.toForm (correctorSubspace d)
        (constantStrainL d) ν hc hαV hβV hαE hβE hV' hE'
        f p.eval hf hpcont hδ.le happrox e g
  have herrseq (n) : dist (J (νseq n) f) (J (νseq n) p.eval) ≤ δ * M := by
    simpa only [J, Real.dist_eq, norm_constantStrain, M, mul_assoc] using
      compressedMeasure_pairing_sub_le (Vseq n).toForm (Eseq n).toForm (correctorSubspace d)
        (constantStrainL d) (νseq n) (hcseq n) hαV hβV hαE hβE (hVs n) (hEs n)
        f p.eval hf hpcont hδ.le happrox e g
  have hpoly := cell_polynomial_tendsto V E Vseq Eseq hαV hβV hαE hβE
    hV hE hVseq hEseq hVconv hEconv ν νseq hc hcseq p e g
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hpoly (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hmid : dist (J (νseq n) p.eval) (J ν p.eval) < ε / 3 := hN n hn
  have hfirst := herrseq n
  have hlast : dist (J ν p.eval) (J ν f) ≤ δ * M := by rwa [dist_comm]
  change dist (J (νseq n) f) (J ν f) < ε
  have htri₁ := dist_triangle (J (νseq n) f) (J (νseq n) p.eval) (J ν f)
  have htri₂ := dist_triangle (J (νseq n) p.eval) (J ν p.eval) (J ν f)
  linarith

end KVApproximation.Spectral
