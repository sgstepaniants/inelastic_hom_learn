module

public import KVApproximation.Analysis.PeriodicFourierEnergy
public import KVApproximation.Analysis.PeriodicFourierCoefficients
public import KVApproximation.Analysis.PeriodicPoincare
public import KVApproximation.Analysis.PeriodicWeakGradient
public import KVApproximation.Analysis.PeriodicSobolevIdentities
public import KVApproximation.Tensor.KornSymbol

/-!
# Periodic Korn and Poincaré inequalities
-/

public section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

/-- Section 3.1, periodic Korn argument: the full gradient is controlled
by its ordinary symmetric part, with the exact squared-norm factor two. -/
theorem HasPeriodicWeakGradient.gradient_sq_norm_le_symmetric {d : ℕ}
    {u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d)}
    {g : Lp (SecondOrder d) 2 (cellMeasure d)}
    (h : HasPeriodicWeakGradient u g) :
    ‖g‖ ^ 2 ≤ 2 * ‖(symmetrizeL d).compLpL 2 (cellMeasure d) g‖ ^ 2 := by
  let s := (symmetrizeL d).compLpL 2 (cellMeasure d) g
  let J := (symmetricSubmodule d).subtypeL
  let A : Lp (SecondOrder d) 2 (cellMeasure d) := J.compLpL 2 (cellMeasure d) s
  have hnorm : ‖A‖ = ‖s‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable A) (Lp.aestronglyMeasurable s)
    filter_upwards [J.coeFn_compLpL s] with y hy
    change ‖(J.compLpL 2 (cellMeasure d) s) y‖ = _
    rw [hy]
    rfl
  have hA : ∀ᵐ y ∂cellMeasure d, ∀ ij : Fin d × Fin d,
      A y ij = (g y ij + g y (ij.2, ij.1)) / 2 := by
    filter_upwards [J.coeFn_compLpL s, (symmetrizeL d).coeFn_compLpL g] with y hJ hs
    intro ij
    change (J.compLpL 2 (cellMeasure d) s) y ij = _
    rw [hJ]
    change (s y).val ij = _
    change ((symmetrizeL d).compLpL 2 (cellMeasure d) g) y = _ at hs
    rw [hs]
    rfl
  have hcoeff (n : Fin d → ℤ) (i j : Fin d) :
      (∫ y, UnitAddTorus.mFourier (-n) y * (A y (i, j) : ℂ) ∂cellMeasure d) =
        ((∫ y, UnitAddTorus.mFourier (-n) y * (g y (i, j) : ℂ) ∂cellMeasure d) +
         (∫ y, UnitAddTorus.mFourier (-n) y * (g y (j, i) : ℂ) ∂cellMeasure d)) / 2 := by
    have hint (ij : Fin d × Fin d) : Integrable
        (fun y => UnitAddTorus.mFourier (-n) y * (g y ij : ℂ)) (cellMeasure d) := by
      have hc : MemLp (UnitAddTorus.mFourier (-n)) 2 (cellMeasure d) :=
        (UnitAddTorus.mFourier (-n)).continuous.memLp_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      exact memLp_one_iff_integrable.mp
        (hc.mul (Complex.ofRealCLM.comp_memLp' ((Lp.memLp g).eval_piLp ij)))
    calc
      _ = ∫ y, (UnitAddTorus.mFourier (-n) y * (g y (i, j) : ℂ) +
          UnitAddTorus.mFourier (-n) y * (g y (j, i) : ℂ)) / 2 ∂cellMeasure d := by
        apply integral_congr_ae
        filter_upwards [hA] with y hy
        rw [hy (i, j)]
        push_cast
        ring
      _ = _ := by rw [integral_div, integral_add (hint (i, j)) (hint (j, i))]
  have hsum := hasSum_le (fun n : Fin d → ℤ => ?_)
    (hasSum_fourier_energy g) ((hasSum_fourier_energy A).mul_left 2)
  · simpa only [hnorm] using hsum
  · simp only [Fintype.sum_prod_type]
    simp_rw [hcoeff, h.fourier_coefficient]
    let a : Fin d → ℂ := fun i => (2 * (Real.pi : ℂ) * Complex.I) *
      ∫ y, UnitAddTorus.mFourier (-n) y * (u y i : ℂ) ∂cellMeasure d
    have heq (i j : Fin d) :
        (2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ)) *
          (∫ y, UnitAddTorus.mFourier (-n) y * (u y i : ℂ) ∂cellMeasure d) =
        a i * ((n j : ℝ) : ℂ) := by
      simp only [a, Complex.ofReal_intCast]
      ring
    simp_rw [heq]
    exact rankOne_sq_norm_le_symmetrized a (fun j => (n j : ℝ))

/-- Section 3.1 (`eq:space_strain_corrector`): the full H¹ norm on
zero-mean periodic displacements admits Korn constant two. -/
theorem periodic_korn_two {d : ℕ} (u : ZeroMeanPeriodicH1 d) :
    ‖u‖ ≤ 2 * ‖correctorGradientL d u‖ := by
  have hw := PeriodicH1.hasWeakGradient (u : PeriodicH1 d)
  have hs := hw.gradient_sq_norm_le_symmetric
  have hp := hw.poincare_sq ((mem_zeroMeanPeriodicSubmodule_iff _).mp u.property)
  have hn := PeriodicH1.norm_sq (u : PeriodicH1 d)
  change ‖PeriodicH1.gradientL d u.val‖ ^ 2 ≤
    2 * ‖correctorGradientL d u‖ ^ 2 at hs
  change ‖u‖ ^ 2 = _ at hn
  nlinarith [norm_nonneg u, norm_nonneg (correctorGradientL d u)]

/-- Section 3.1 (`eq:space_strain_corrector`): periodic Korn inequality
on the zero-mean displacement space, with the full H¹ norm. -/
theorem periodic_korn (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ZeroMeanPeriodicH1 d,
      ‖u‖ ≤ C * ‖correctorGradientL d u‖ :=
  ⟨2, by norm_num, fun u => periodic_korn_two u⟩

end KVApproximation.Analysis
