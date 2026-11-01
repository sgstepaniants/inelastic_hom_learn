module

public import KVApproximation.KelvinVoigt.ApproximationProblem
public import KVApproximation.KelvinVoigt.PronyProblem
public import KVApproximation.KelvinVoigt.MaterialCompactness
public import KVApproximation.Tensor.MandelFiniteIsometry
public import KVApproximation.NeuralOperators.CoordinateResponseApproximation
public import KVApproximation.NeuralOperators.UniformPronyStability
public import KVApproximation.Dynamics.PronyStateBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Neural approximation from a continuous Prony family
-/

public section

open MeasureTheory
open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.NeuralOperators

namespace KVApproximation.KelvinVoigt

/-- Theorem 4.4, `eq:ua_error_tolerances`, with trapping radius one. -/
private theorem response_tolerances {n : ℕ} (hn : 0 < n) {gap r : ℝ}
    (hgap : 0 < gap) (hr : 0 < r) :
    ∃ εF εG : ℝ, 0 < εF ∧ 0 < εG ∧ εG ≤ r * 1 ∧
      εF + Real.sqrt n * εG / r ≤ gap := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  let εG := min (r / 2) (r * gap / (2 * Real.sqrt n))
  have hG : 0 < εG := lt_min (by positivity) (by positivity)
  refine ⟨gap / 2, εG, by positivity, hG, ?_, ?_⟩
  · have h := min_le_left (r / 2) (r * gap / (2 * Real.sqrt n))
    dsimp only [εG]
    linarith
  · have h := (le_div_iff₀ (show 0 < 2 * Real.sqrt n by positivity)).mp
      (show εG ≤ r * gap / (2 * Real.sqrt n) from min_le_right _ _)
    have hg : Real.sqrt n * εG / r ≤ gap / 2 := (div_le_iff₀ hr).mpr (by nlinarith)
    linarith

/-- Theorem 4.4, final triangle inequality after the two error budgets. -/
private theorem uniformlyApproximates_of_prony_error
    {d n nξ : ℕ} {αV βV γV αE βE γE δ ε εIV εNO : ℝ}
    {hαV : 0 < αV} {hαE : 0 < αE}
    (C : CellFamily d αV βV γV αE βE γE hαV hαE)
    (P : PronyModel (admissibleMaterials d αV βV γV αE βE γE) (Symmetric d) n)
    (F : C(StressInput (Symmetric d) (InternalState nξ) × Material d, Symmetric d))
    (G : C(KineticInput (Symmetric d) (InternalState nξ) × Material d, InternalState nξ))
    (hεIV : 0 ≤ εIV) (hεNO : 0 ≤ εNO) (hbudget : εNO + εIV ≤ ε)
    (hP : uniformPronyError C P δ ≤ ENNReal.ofReal εIV)
    (hNO : ∀ (M : admissibleMaterials d αV βV γV αE βE γE)
      (e : BoundedTrajectory (Symmetric d)), e.Admissible βE βV δ →
        ∃ q : BoundedTrajectory (InternalState nξ), IsResponseSolution G M.val e q ∧
          (∀ q', IsResponseSolution G M.val e q' → q.Agree q') ∧
          eLpNorm (fun t => stressAlong F M.val e q t - P.stress M e t) ⊤ timeMeasure ≤
            ENNReal.ofReal εNO) : UniformlyApproximates C F G δ ε := by
  intro M e he
  obtain ⟨q, hq, huniq, herr⟩ := hNO M e he
  refine ⟨q, hq, ?_, ?_⟩
  · intro q' hq'
    obtain ⟨hv, hd⟩ := huniq q' hq'
    exact ⟨fun t ht => (hv t ht).symm, hd.symm⟩
  · have hprony : eLpNorm (fun t => constitutiveStress (C M) e t - P.stress M e t)
        ⊤ timeMeasure ≤ ENNReal.ofReal εIV :=
      (le_iSup_of_le M (le_iSup_of_le e (by simp only [iSup_pos he, le_refl]))).trans hP
    have heq : (fun t => stressAlong F M.val e q t - constitutiveStress (C M) e t) =
        (fun t => stressAlong F M.val e q t - P.stress M e t) -
          (fun t => constitutiveStress (C M) e t - P.stress M e t) := by
      funext t
      simp only [Pi.sub_apply]
      abel
    rw [heq]
    exact (eLpNorm_sub_le (show (1 : ENNReal) ≤ ⊤ from le_top)).trans
      ((add_le_add herr hprony).trans (by
        rw [← ENNReal.ofReal_add hεNO hεIV]
        exact ENNReal.ofReal_le_ofReal hbudget))

/-- Theorem 4.4, Appendix B.3 and Remark 4.6: a continuous Prony family
with positive shared rates and a strict uniform stress-error gap admits
the paper's neural response construction without adding states. -/
theorem continuous_prony_neural_approximation
    {d : ℕ} (hd : d ∈ ({1, 2, 3} : Set ℕ))
    {αV βV γV αE βE γE δ ε rateLower : ℝ}
    (hαV : 0 < αV) (hVorder : αV ≤ βV) (hγV : 0 < γV)
    (hαE : 0 < αE) (hEorder : αE ≤ βE) (hγE : 0 < γE)
    (hδ : 0 < δ) (hε : 0 < ε)
    (C : CellFamily d αV βV γV αE βE γE hαV hαE)
    {n : ℕ} (hn : 0 < n)
    (P : PronyModel (admissibleMaterials d αV βV γV αE βE γE) (Symmetric d) n)
    (hV : Continuous P.viscosity) (hE : Continuous P.elasticity)
    (hcoef : ∀ k, Continuous (P.coefficient k))
    (hrateLower : 0 < rateLower) (hrate : ∀ k, rateLower ≤ P.rate k)
    (herror : uniformPronyError C P δ < ENNReal.ofReal ε)
    (Fclass : StressResponseClass d (n * strainDimension d))
    (Gclass : KineticResponseClass d (n * strainDimension d))
    (hF : HasUniversalApproximation Fclass) (hG : HasLocallyLipschitzApproximation Gclass) :
    ∃ F ∈ Fclass, ∃ G ∈ Gclass, UniformlyApproximates C F G δ ε := by
  have hβV : 0 < βV := hαV.trans_le hVorder
  have hβE : 0 < βE := hαE.trans_le hEorder
  have hL := isCompact_admissibleMaterials hd hαV hVorder hγV hαE hEorder hγE
  let : CompactSpace (admissibleMaterials d αV βV γV αE βE γE) :=
    isCompact_iff_compactSpace.mp hL
  obtain ⟨T, _hT⟩ := scalarBlockStrainMandel_isometry n d
  obtain ⟨εIV, hmax, hεIV⟩ := exists_between
    (max_lt hε (ENNReal.toReal_lt_of_lt_ofReal herror))
  have herrorIV := (le_max_right 0 (uniformPronyError C P δ).toReal).trans_lt hmax
  have hεIVpos : 0 < εIV := (le_max_left 0 (uniformPronyError C P δ).toReal).trans_lt hmax
  have hP : uniformPronyError C P δ ≤ ENNReal.ofReal εIV :=
    (ENNReal.le_ofReal_iff_toReal_le herror.ne_top hεIVpos.le).mpr herrorIV.le
  obtain ⟨εF, εG, hεF, hεG, hmargin, hbudget⟩ :=
    response_tolerances hn (sub_pos.mpr hεIV) hrateLower
  obtain ⟨δIV, hδIV, hIV⟩ := prony_state_uniform_bound P Set.univ isCompact_univ
    (fun k => (hcoef k).continuousOn) hβE hβV hδ
    (fun k => hrateLower.trans_le (hrate k))
  obtain ⟨F, hFmem, G, hGmem, hFapprox, hGapprox, hGlip⟩ :=
    prony_responses_approximate_in_coordinates _ hL P T hV hE hcoef
      hβE hβV hδ (add_pos hδIV zero_lt_one) hεF hεG Fclass Gclass hF hG
  obtain ⟨q, hq, _hstate, hstress⟩ := uniform_prony_response_stability P Subtype.val T
    hβE hβV hrateLower hrate hδIV (fun a => hIV a (Set.mem_univ a))
    zero_lt_one hεF hεG hmargin F G hGlip hFapprox hGapprox
  refine ⟨F, hFmem, G, hGmem, ?_⟩
  apply uniformlyApproximates_of_prony_error C P F G hεIVpos.le
    (sub_nonneg.mpr hεIV.le) (by linarith) hP
  intro M e he
  refine ⟨q M ⟨e, he⟩, (hq M ⟨e, he⟩).1, (hq M ⟨e, he⟩).2, ?_⟩
  have herr := (iSup_le_iff.mp (iSup_le_iff.mp hstress M)) ⟨e, he⟩
  exact herr.trans (ENNReal.ofReal_le_ofReal hbudget)

end KVApproximation.KelvinVoigt
