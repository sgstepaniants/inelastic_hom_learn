module

public import KVApproximation.Analysis.PeriodicBoxes
public import KVApproximation.Analysis.PeriodicRescaling
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite-exponent bounds for periodic rescaling

The measure of one rescaled cell is exact. A finite cover of a bounded
domain controls the pushforward measure uniformly in the scale; taking
the square root then gives the L² estimate for oscillating correctors.
-/

public section

open MeasureTheory Set

namespace KVApproximation.Analysis

private theorem measurePreserving_unitBox {d : ℕ} (a : Fin d → ℝ) :
    MeasurePreserving (@toCell d) (volume.restrict (periodicBox a 1))
      (cellMeasure d) := by
  have hc : MeasurePreserving
      (fun x : Fin d → ℝ => (fun i => (x i : UnitAddCircle)))
      (volume.restrict (Set.univ.pi fun i => Ioc (a i) (a i + 1)))
      (cellMeasure d) := by
    change MeasurePreserving _
      ((Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict _) _
    rw [Measure.restrict_pi_pi]
    apply measurePreserving_pi
    intro i
    simpa [volume, AddCircle.haarAddCircle] using AddCircle.measurePreserving_mk 1 (a i)
  have hset : MeasurableSet (Set.univ.pi fun i => Ioc (a i) (a i + 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hpre : (fun x : EuclideanSpace ℝ (Fin d) => x.ofLp) ⁻¹'
      (Set.univ.pi fun i => Ioc (a i) (a i + 1)) = periodicBox a 1 := by
    ext x
    simp [periodicBox, Set.pi]
  rw [← hpre]
  exact hc.comp ((PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage hset)

/-- Theorem 3.1, static periodic homogenization: projection of one
rescaled half-open cell has exactly its physical volume times the
normalized torus measure. -/
theorem map_scaledToCell_restrict_periodicBox {d : ℕ} (a : Fin d → ℝ)
    {ε : ℝ} (hε : ε ≠ 0) :
    Measure.map (fun x : EuclideanSpace ℝ (Fin d) => toCell (ε⁻¹ • x))
      (volume.restrict (periodicBox a ε)) =
      ENNReal.ofReal (|ε| ^ d) • cellMeasure d := by
  have hd : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ε⁻¹ • x) :=
    measurable_const_smul _
  have hq : Measurable (@toCell d) := (measurePreserving_unitBox a).measurable
  have hm : MeasurableSet (periodicBox a 1) := by
    simp only [periodicBox, inv_one, one_smul]
    simpa only [Set.ofPred_forall] using
      (MeasurableSet.iInter fun i : Fin d =>
        show MeasurableSet {x : EuclideanSpace ℝ (Fin d) |
            a i < x i ∧ x i ≤ a i + 1} from
          measurableSet_Ioc.preimage
            (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable)
  have hb : periodicBox a ε =
      (fun x : EuclideanSpace ℝ (Fin d) => ε⁻¹ • x) ⁻¹' periodicBox a 1 := by
    ext x
    simp [periodicBox]
  change Measure.map ((@toCell d) ∘ fun x => ε⁻¹ • x) _ = _
  rw [hb, ← Measure.map_map hq hd, ← Measure.restrict_map hd hm,
    Measure.map_addHaar_smul volume (inv_ne_zero hε)]
  simp only [finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_pow]
  rw [Measure.restrict_smul, Measure.map_smul _ hq.aemeasurable,
    (measurePreserving_unitBox a).map_eq]

private theorem periodicBoxes_cover {d : ℕ} {R ε : ℝ} (hε : 0 < ε) :
    {x : EuclideanSpace ℝ (Fin d) | ‖x‖ ≤ R} ⊆
      ⋃ j : Fin d → Fin (Nat.ceil (2 * R / ε) + 1),
        periodicBox (fun i => (j i : ℝ) - R / ε - 1) ε := by
  intro x hx
  have hcoord (i : Fin d) : |x i| ≤ R :=
    (PiLp.norm_apply_le x i).trans hx
  have hs (i : Fin d) :
      0 ≤ (ε⁻¹ • x) i + R / ε ∧ (ε⁻¹ • x) i + R / ε ≤ 2 * R / ε := by
    have hi := abs_le.mp (hcoord i)
    simp only [PiLp.smul_apply, smul_eq_mul]
    constructor
    · rw [← div_eq_inv_mul]
      have hl := div_le_div_of_nonneg_right hi.1 hε.le
      rw [neg_div] at hl
      linarith
    · rw [← div_eq_inv_mul]
      have := div_le_div_of_nonneg_right hi.2 hε.le
      rw [mul_div_assoc]
      linarith
  let j : Fin d → Fin (Nat.ceil (2 * R / ε) + 1) := fun i =>
    ⟨Nat.ceil ((ε⁻¹ • x) i + R / ε),
      Nat.lt_succ_of_le (Nat.ceil_mono (hs i).2)⟩
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  intro i
  have hl := Nat.ceil_lt_add_one (hs i).1
  have hu := Nat.le_ceil ((ε⁻¹ • x) i + R / ε)
  change (Nat.ceil ((ε⁻¹ • x) i + R / ε) : ℝ) - R / ε - 1 < _ ∧
    _ ≤ (Nat.ceil ((ε⁻¹ • x) i + R / ε) : ℝ) - R / ε - 1 + 1
  constructor <;> linarith

/-- Theorem 3.1, static periodic homogenization: a bounded physical
domain has a uniform rescaled cell-measure bound, chosen before the
positive scale at most one. -/
theorem exists_rescaling_measure_bound {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Measure.map (fun x : EuclideanSpace ℝ (Fin d) => toCell (ε⁻¹ • x))
        (volume.restrict Ω) ≤ ENNReal.ofReal K • cellMeasure d := by
  classical
  obtain ⟨R, hR, hΩR⟩ := hΩ.exists_pos_norm_le
  refine ⟨(2 * R + 2) ^ d, by positivity, ?_⟩
  intro ε hε hε₁
  let N := Nat.ceil (2 * R / ε) + 1
  let B : (Fin d → Fin N) → Set (EuclideanSpace ℝ (Fin d)) := fun j =>
    periodicBox (fun i => (j i : ℝ) - R / ε - 1) ε
  let q : EuclideanSpace ℝ (Fin d) → PeriodicCell d := fun x => toCell (ε⁻¹ • x)
  have hq : Measurable q := (quasiMeasurePreserving_scaledToCell hε.ne').measurable
  have hcover : Ω ⊆ ⋃ j, B j :=
    fun x hx => periodicBoxes_cover hε (hΩR x hx)
  have hN : ε * (N : ℝ) ≤ 2 * R + 2 := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * R / ε by positivity)
    have hm := mul_le_mul_of_nonneg_left hc.le hε.le
    have he : ε * (2 * R / ε) = 2 * R := mul_div_cancel₀ _ hε.ne'
    dsimp [N]
    push_cast
    nlinarith
  have hcell (j : Fin d → Fin N) :
      Measure.map q (volume.restrict (B j)) =
        ENNReal.ofReal (ε ^ d) • cellMeasure d := by
    simpa only [abs_of_pos hε] using
      map_scaledToCell_restrict_periodicBox (fun i => (j i : ℝ) - R / ε - 1) hε.ne'
  have hsum : (∑ j : Fin d → Fin N, ENNReal.ofReal (ε ^ d) • cellMeasure d) =
      ENNReal.ofReal ((ε * (N : ℝ)) ^ d) • cellMeasure d := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [← smul_assoc, nsmul_eq_mul]
    congr 1
    simp [mul_pow, ENNReal.ofReal_mul (pow_nonneg hε.le d), mul_comm]
  calc
    Measure.map q (volume.restrict Ω) ≤
        Measure.map q (volume.restrict (⋃ j, B j)) :=
      Measure.map_mono (Measure.restrict_mono_set volume hcover) hq
    _ ≤ Measure.map q (Measure.sum fun j => volume.restrict (B j)) :=
      Measure.map_mono Measure.restrict_iUnion_le hq
    _ = ∑ j : Fin d → Fin N, ENNReal.ofReal (ε ^ d) • cellMeasure d := by
      rw [Measure.map_sum hq.aemeasurable, Measure.sum_fintype]
      simp_rw [hcell]
    _ = ENNReal.ofReal ((ε * (N : ℝ)) ^ d) • cellMeasure d := hsum
    _ ≤ ENNReal.ofReal ((2 * R + 2) ^ d) • cellMeasure d := by
      apply Measure.le_iff.mpr
      intro s hs
      simp only [Measure.smul_apply, smul_eq_mul]
      gcongr

/-- Theorem 3.1, oscillating corrector bounds: periodic rescaling is
uniformly bounded from cell L² to L² on any bounded physical domain.
The constant precedes both the scale and the field. -/
theorem exists_eLpNorm_two_rescalePeriodic_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : PeriodicCell d → F, AEStronglyMeasurable f (cellMeasure d) →
        eLpNorm (rescalePeriodic f ε) 2 (volume.restrict Ω) ≤
          ENNReal.ofReal C * eLpNorm f 2 (cellMeasure d) := by
  obtain ⟨K, hK, hbound⟩ := exists_rescaling_measure_bound hΩ
  refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hK, ?_⟩
  intro ε hε hε₁ f hf
  have hmap := hbound ε hε hε₁
  have hq := (quasiMeasurePreserving_scaledToCell (d := d) hε.ne').measurable
  have hfmap := (hf.smul_measure (ENNReal.ofReal K)).mono_measure hmap
  calc
    eLpNorm (rescalePeriodic f ε) 2 (volume.restrict Ω) =
        eLpNorm f 2 (Measure.map (fun x => toCell (ε⁻¹ • x)) (volume.restrict Ω)) :=
      (eLpNorm_map_measure hfmap hq.aemeasurable).symm
    _ ≤ eLpNorm f 2 (ENNReal.ofReal K • cellMeasure d) := eLpNorm_mono_measure f hmap
    _ = ENNReal.ofReal (Real.sqrt K) * eLpNorm f 2 (cellMeasure d) := by
      rw [eLpNorm_smul_measure_of_ne_top (by norm_num) f _ hf]
      simp [ENNReal.ofReal_rpow_of_pos hK, Real.sqrt_eq_rpow, one_div]

/-- Theorem 3.1, oscillating correctors: an L² periodic field remains
L² on each bounded physical domain after rescaling. -/
theorem memLp_two_rescalePeriodic {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : Bornology.IsBounded Ω) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    {f : PeriodicCell d → F} (hf : MemLp f 2 (cellMeasure d)) :
    MemLp (rescalePeriodic f ε) 2 (volume.restrict Ω) := by
  obtain ⟨C, _, hC⟩ := exists_eLpNorm_two_rescalePeriodic_bound (F := F) hΩ
  exact (hC ε hε hε₁ f hf.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

end KVApproximation.Analysis
