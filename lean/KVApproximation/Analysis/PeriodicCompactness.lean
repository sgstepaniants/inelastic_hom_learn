module

public import KVApproximation.Analysis.PeriodicCell
public import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Compactness from periodic translations

The quotient map sends small Euclidean balls to neighborhoods of zero on the
torus. This transfers a Euclidean translation modulus to the group translations
in the Fréchet–Kolmogorov criterion; compactness of the cell supplies tightness.
-/

public section

open MeasureTheory
open scoped Topology

namespace KVApproximation.Analysis

private theorem isOpenQuotientMap_toCell (d : ℕ) :
    IsOpenQuotientMap (toCell (d := d)) := by
  have hq : IsOpenQuotientMap
      (fun x : Fin d → ℝ => fun i => (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  exact hq.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap

/-- Lemma B.2, compactness criterion for the cited periodic BV embedding:
bounded families with uniformly small Euclidean translation increments have
compact closure in finite-exponent Lp on the cell. -/
theorem isCompact_closure_of_periodic_translations {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {S : Set (Lp F p (cellMeasure d))} {M : ENNReal} (hM : M ≠ ⊤)
    (hbound : ∀ A ∈ S, eLpNorm A p (cellMeasure d) ≤ M)
    (htrans : ∀ ε : ENNReal, 0 < ε → ∃ δ > 0,
      ∀ A ∈ S, ∀ h : EuclideanSpace ℝ (Fin d), ‖h‖ < δ →
        eLpNorm (fun y => A (y + toCell h) - A y) p (cellMeasure d) ≤ ε) :
    IsCompact (closure S) := by
  let : (cellMeasure d).IsAddHaarMeasure := by unfold cellMeasure; infer_instance
  apply TauCeti.isCompact_closure_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl
    hp (s := Set.univ) isCompact_univ.isBounded
    (fun _ _ => Filter.Eventually.of_forall fun _ => by simp) hM hbound
  intro ε hε
  obtain ⟨δ, hδ, hδtrans⟩ := htrans ε hε
  have hzero : toCell (0 : EuclideanSpace ℝ (Fin d)) = (0 : PeriodicCell d) := by
    ext i
    rfl
  have himage : toCell '' Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ ∈
      𝓝 (0 : PeriodicCell d) := by
    simpa only [hzero] using
      (isOpenQuotientMap_toCell d).isOpenMap.image_mem_nhds (Metric.ball_mem_nhds 0 hδ)
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.mem_nhds_iff.mp himage
  refine ⟨ρ, hρ, fun A hA h hh => ?_⟩
  obtain ⟨v, hv, hveq⟩ := hsmall (by simpa only [Metric.mem_ball, dist_zero_right] using hh)
  rw [← hveq]
  exact hδtrans A hA v (by simpa only [Metric.mem_ball, dist_zero_right] using hv)

end KVApproximation.Analysis
