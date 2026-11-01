module

public import KVApproximation.Analysis.PeriodicFourierSynthesis
public import KVApproximation.Analysis.PeriodicFourierCoefficients
public import KVApproximation.Analysis.PeriodicWeakGradient

/-!
# Smooth density for periodic weak gradients
-/

public section

noncomputable section

open MeasureTheory
open KVApproximation.Tensor

namespace KVApproximation.Analysis

private def valueJetL (d : ℕ) : EuclideanSpace ℝ (Fin d) →L[ℝ] PeriodicJet d :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ _ _)

private def gradientJetL (d : ℕ) : SecondOrder d →L[ℝ] PeriodicJet d :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ _ _)

private def pairJet {d : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d))
    (g : Lp (SecondOrder d) 2 (cellMeasure d)) : PeriodicJetField d :=
  (valueJetL d).compLpL 2 (cellMeasure d) u +
    (gradientJetL d).compLpL 2 (cellMeasure d) g

private theorem pairJet_ae {d : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d))
    (g : Lp (SecondOrder d) 2 (cellMeasure d)) :
    ∀ᵐ y ∂cellMeasure d, pairJet u g y = WithLp.toLp 2 (u y, g y) := by
  filter_upwards [Lp.coeFn_add ((valueJetL d).compLpL 2 (cellMeasure d) u)
      ((gradientJetL d).compLpL 2 (cellMeasure d) g),
    (valueJetL d).coeFn_compLpL u, (gradientJetL d).coeFn_compLpL g] with y ha hv hg
  change (((valueJetL d).compLpL 2 (cellMeasure d) u +
    (gradientJetL d).compLpL 2 (cellMeasure d) g) y) = _
  rw [ha]
  change ((valueJetL d).compLpL 2 (cellMeasure d) u) y +
    ((gradientJetL d).compLpL 2 (cellMeasure d) g) y = _
  rw [hv, hg]
  change WithLp.toLp 2 (u y, (0 : SecondOrder d)) +
    WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), g y) = _
  simp only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]

private theorem value_pairJet {d : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d))
    (g : Lp (SecondOrder d) 2 (cellMeasure d)) :
    (WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).compLpL
      2 (cellMeasure d) (pairJet u g) = u := by
  apply Lp.ext
  filter_upwards
    [(WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL (pairJet u g),
      pairJet_ae u g] with y hp hj
  rw [hp, hj]
  rfl

private theorem gradient_pairJet {d : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d))
    (g : Lp (SecondOrder d) 2 (cellMeasure d)) :
    (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).compLpL
      2 (cellMeasure d) (pairJet u g) = g := by
  apply Lp.ext
  filter_upwards
    [(WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin d)) (SecondOrder d)).coeFn_compLpL (pairJet u g),
      pairJet_ae u g] with y hp hj
  rw [hp, hj]
  rfl

/-- Section 3.1: completion of smooth periodic jets agrees with the
distributional definition of the periodic first-order Sobolev space. -/
theorem periodicH1_iff_weakGradient {d : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (cellMeasure d))
    (g : Lp (SecondOrder d) 2 (cellMeasure d)) :
    HasPeriodicWeakGradient u g ↔
      ∃ w : PeriodicH1 d, PeriodicH1.valueL d w = u ∧ PeriodicH1.gradientL d w = g := by
  constructor
  · intro h
    let m (n : Fin d → ℤ) := realFourierMode n (fun i =>
      ∫ y, UnitAddTorus.mFourier (-n) y * (u y i : ℂ) ∂cellMeasure d)
    let q (n : Fin d → ℤ) := realFourierMode n (fun ij =>
      ∫ y, UnitAddTorus.mFourier (-n) y * (g y ij : ℂ) ∂cellMeasure d)
    have hgrad (n : Fin d → ℤ) (y : PeriodicCell d) :
        periodicGradient (m n) y = q n y := by
      apply PiLp.ext
      intro ij
      change (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) =>
          realFourierMode n (fun i =>
            ∫ t, UnitAddTorus.mFourier (-n) t * (u t i : ℂ) ∂cellMeasure d) (toCell z))
          (cellRepresentative y) (WithLp.toLp 2 (Pi.single ij.2 (1 : ℝ)))) ij.1 = _
      rw [fderiv_realFourierMode_lift_apply, toCell_cellRepresentative]
      change ((∫ t, UnitAddTorus.mFourier (-n) t * (u t ij.1 : ℂ) ∂cellMeasure d) *
          (2 * (Real.pi : ℂ) * Complex.I * (n ij.2 : ℂ)) * UnitAddTorus.mFourier n y).re =
        ((∫ t, UnitAddTorus.mFourier (-n) t * (g t ij : ℂ) ∂cellMeasure d) *
          UnitAddTorus.mFourier n y).re
      rw [h.fourier_coefficient n ij.1 ij.2]
      congr 1
      ring
    let term (n : Fin d → ℤ) : PeriodicJetField d :=
      pairJet ((m n).toLp 2 (cellMeasure d) ℝ) ((q n).toLp 2 (cellMeasure d) ℝ)
    have hterm (n : Fin d → ℤ) : term n ∈ periodicH1Submodule d := by
      apply (Submodule.span ℝ (smoothPeriodicJets d)).le_topologicalClosure
      apply Submodule.subset_span
      refine ⟨m n, contDiff_realFourierMode_lift n _, ?_⟩
      filter_upwards [pairJet_ae ((m n).toLp 2 (cellMeasure d) ℝ)
          ((q n).toLp 2 (cellMeasure d) ℝ),
        (m n).coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d),
        (q n).coeFn_toLp (p := 2) (𝕜 := ℝ) (cellMeasure d)] with y hp hm hq
      change pairJet ((m n).toLp 2 (cellMeasure d) ℝ) ((q n).toLp 2 (cellMeasure d) ℝ) y = _
      rw [hp, hm, hq, hgrad]
    have hsum : HasSum term (pairJet u g) :=
      (((valueJetL d).compLpL 2 (cellMeasure d)).hasSum (hasSum_realFourier_series u)).add
        (((gradientJetL d).compLpL 2 (cellMeasure d)).hasSum (hasSum_realFourier_series g))
    have hmem : pairJet u g ∈ periodicH1Submodule d :=
      (periodicH1Submodule d).isClosed.mem_of_tendsto hsum
        (Filter.Eventually.of_forall fun s =>
          (periodicH1Submodule d).sum_mem fun n _ => hterm n)
    refine ⟨⟨pairJet u g, hmem⟩, ?_, ?_⟩
    · exact value_pairJet u g
    · exact gradient_pairJet u g
  · rintro ⟨w, rfl, rfl⟩
    exact PeriodicH1.hasWeakGradient w

end KVApproximation.Analysis
