module

public import KVApproximation.KelvinVoigt.StripBV
public import KVApproximation.KelvinVoigt.StripConvergence
public import KVApproximation.KelvinVoigt.MaterialTopology

/-!
# A convergent family in one admissible material class
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.KelvinVoigt

/-- Proposition 4.7 (`prop:no_spectral_stability`), admissibility and convergence:
the identity material and all thin-strip materials belong to one fixed
BV-bounded class and converge in its actual L² topology and both L¹ seminorms. -/
theorem exists_strip_material_family {d : ℕ} (i : Fin d) :
    ∃ M : admissibleMaterials d 1 1 (‖identityElasticity d‖ + 1)
        1 2 (4 * ‖identityElasticity d‖ + 1),
      ∃ Mseq : ℕ → admissibleMaterials d 1 1 (‖identityElasticity d‖ + 1)
          1 2 (4 * ‖identityElasticity d‖ + 1),
        (∀ᵐ y ∂cellMeasure d, M.val.1 y = identityElasticity d ∧
          M.val.2 y = identityElasticity d) ∧
        (∀ n, ∀ᵐ y ∂cellMeasure d,
          (Mseq n).val.1 y = identityElasticity d ∧
            (Mseq n).val.2 y = stripElasticity i n y) ∧
        Tendsto Mseq atTop (𝓝 M) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.1 y - M.val.1 y)
          1 (cellMeasure d)) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (fun y => (Mseq n).val.2 y - M.val.2 y)
          1 (cellMeasure d)) atTop (𝓝 0) := by
  let Iraw : PeriodicCell d → Elasticity d := fun _ => identityElasticity d
  let hI : MemLp Iraw 2 (cellMeasure d) := memLp_const _
  let A : CoefficientField d 2 := hI.toLp Iraw
  have hArep : A =ᵐ[cellMeasure d] Iraw := hI.coeFn_toLp
  have hAtop : MemLp A ⊤ (cellMeasure d) :=
    (memLp_top_const (identityElasticity d)).ae_eq hArep.symm
  have hA11 : HasFieldBounds 1 1 A := by
    let htop : MemLp Iraw ⊤ (cellMeasure d) := memLp_top_const _
    have hb : HasFieldBounds 1 1 (htop.toLp Iraw) := by
      apply (hasFieldBounds_iff_ae _).2
      filter_upwards [htop.coeFn_toLp] with y hy
      intro e
      rw [hy]
      simp only [Iraw, action_identityElasticity, real_inner_self_eq_norm_sq, one_mul]
      exact ⟨le_rfl, le_rfl⟩
    exact (hb.congr htop.coeFn_toLp).congr hArep.symm
  have hA12 : HasFieldBounds 1 2 A := by
    intro e
    refine ⟨(hA11 e).1, (hA11 e).2.trans ?_⟩
    nlinarith [sq_nonneg ‖e‖]
  have hABV : periodicBVNorm A = ENNReal.ofReal ‖identityElasticity d‖ :=
    (periodicBVNorm_congr hArep).trans (periodicBVNorm_identityElasticity d)
  have hABVvis : periodicBVNorm A ≤ ENNReal.ofReal (‖identityElasticity d‖ + 1) := by
    rw [hABV]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
  have hABVelas : periodicBVNorm A ≤ ENNReal.ofReal (4 * ‖identityElasticity d‖ + 1) := by
    rw [hABV]
    exact ENNReal.ofReal_le_ofReal (by linarith [norm_nonneg (identityElasticity d)])
  let hB (n : ℕ) : MemLp (stripElasticity i n) 2 (cellMeasure d) :=
    (memLp_stripElasticity i n).mono_exponent le_top
  let B (n : ℕ) : CoefficientField d 2 := (hB n).toLp (stripElasticity i n)
  have hBrep (n : ℕ) : B n =ᵐ[cellMeasure d] stripElasticity i n := (hB n).coeFn_toLp
  have hBtop (n : ℕ) : MemLp (B n) ⊤ (cellMeasure d) :=
    (memLp_stripElasticity i n).ae_eq (hBrep n).symm
  have hBbounds (n : ℕ) : HasFieldBounds 1 2 (B n) :=
    (hasFieldBounds_stripElasticity i n).congr (hBrep n).symm
  have hBBV (n : ℕ) : periodicBVNorm (B n) ≤ ENNReal.ofReal (4 * ‖identityElasticity d‖ + 1) := by
    rw [periodicBVNorm_congr (hBrep n)]
    exact (periodicBVNorm_stripElasticity_le i n).trans
      (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one))
  have hM : (A, A) ∈ admissibleMaterials d 1 1 (‖identityElasticity d‖ + 1)
      1 2 (4 * ‖identityElasticity d‖ + 1) :=
    ⟨hAtop, hAtop, hA11, hA12, hABVvis, hABVelas⟩
  have hMs (n : ℕ) : (A, B n) ∈ admissibleMaterials d 1 1 (‖identityElasticity d‖ + 1)
      1 2 (4 * ‖identityElasticity d‖ + 1) :=
    ⟨hAtop, hBtop n, hA11, hBbounds n, hABVvis, hBBV n⟩
  let M : admissibleMaterials d 1 1 (‖identityElasticity d‖ + 1)
      1 2 (4 * ‖identityElasticity d‖ + 1) := ⟨(A, A), hM⟩
  let Mseq (n : ℕ) : admissibleMaterials d 1 1 (‖identityElasticity d‖ + 1)
      1 2 (4 * ‖identityElasticity d‖ + 1) := ⟨(A, B n), hMs n⟩
  have hBconv : Tendsto B atTop (𝓝 A) := by
    apply tendsto_iff_dist_tendsto_zero.2
    have hdist (n : ℕ) : dist (B n) A =
        (eLpNorm (fun y => stripElasticity i n y - identityElasticity d) 2 (cellMeasure d)).toReal := by
      rw [Lp.dist_def]
      congr 1
      exact eLpNorm_congr_ae ((hBrep n).sub hArep)
    simp only [hdist]
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp
        (tendsto_eLpNorm_stripElasticity_sub_identity i
          (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤))
  have hMconv : Tendsto Mseq atTop (𝓝 M) :=
    tendsto_subtype_rng.2 (tendsto_const_nhds.prodMk_nhds hBconv)
  exact ⟨M, Mseq, hArep.and hArep, fun n => hArep.and (hBrep n), hMconv,
    material_L1_tendsto hMconv⟩

end KVApproximation.KelvinVoigt
