module

public import KVApproximation.Dynamics.PronyModel
public import KVApproximation.Dynamics.DampedResponseProperties
public import KVApproximation.Dynamics.TrajectoryBounds
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Data.Finset.Max

/-!
# Uniform bounds for the Prony internal variables
-/

public section

open MeasureTheory

namespace KVApproximation.Dynamics

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma B.11 (`lem:ua_step3_targets`), quantitative estimate in its proof:
coefficient bounds and a positive common rate control the Euclidean block norm. -/
theorem prony_state_bound {n : ℕ} (P : PronyModel M E n) (a : M)
    {βE βV δ rateLower : ℝ} (hβE : 0 < βE) (hβV : 0 < βV)
    (hδ : 0 ≤ δ) (hRateLower : 0 < rateLower) (hRate : ∀ k, rateLower ≤ P.rate k)
    (C : Fin n → ℝ) (hC : ∀ k, 0 ≤ C k) (hcoef : ∀ k, ‖P.coefficient k a‖ ≤ C k)
    (e : BoundedTrajectory E) (he : e.Admissible βE βV δ) {t : ℝ} (ht : 0 ≤ t) :
    ‖P.state a e t‖ ≤ δ / (βV * rateLower) * Real.sqrt (∑ k, C k ^ 2) := by
  have hvel : e.velocityBound ≤ δ / βV := by
    apply (le_div_iff₀ hβV).mpr
    have hvalue : 0 ≤ βE * e.valueBound := mul_nonneg hβE.le ENNReal.toReal_nonneg
    change βE * e.valueBound + βV * e.velocityBound ≤ δ at he
    linarith
  let D := δ / (βV * rateLower)
  have hD : 0 ≤ D := div_nonneg hδ (mul_nonneg hβV.le hRateLower.le)
  have hblock (k : Fin n) : ‖P.state a e t k‖ ≤ D * C k := by
    have hforce : ∀ᵐ s ∂timeMeasure,
        ‖P.coefficient k a (e.velocity s)‖ ≤ C k * (δ / βV) := by
      filter_upwards [e.norm_velocity_ae_le] with s hs
      exact ((P.coefficient k a).le_opNorm _).trans
        (mul_le_mul (hcoef k) (hs.trans hvel) (norm_nonneg _) (hC k))
    have hM : 0 ≤ C k * (δ / βV) := mul_nonneg (hC k) (div_nonneg hδ hβV.le)
    calc
      _ ≤ (C k * (δ / βV)) * (1 - Real.exp (-P.rate k * t)) / P.rate k :=
        norm_dampedResponse_le _ (hRateLower.trans_le (hRate k)) ht hforce
      _ ≤ (C k * (δ / βV)) / P.rate k := div_le_div_of_nonneg_right
        (by nlinarith [Real.exp_pos (-P.rate k * t)]) (hRateLower.le.trans (hRate k))
      _ ≤ (C k * (δ / βV)) / rateLower :=
        div_le_div_of_nonneg_left hM hRateLower (hRate k)
      _ = D * C k := by dsimp only [D]; ring
  rw [PiLp.norm_eq_of_L2]
  calc
    _ ≤ Real.sqrt (∑ k : Fin n, (D * C k) ^ 2) :=
      Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hblock k) 2)
    _ = D * Real.sqrt (∑ k, C k ^ 2) := by
      simp only [mul_pow, ← Finset.mul_sum]
      rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD]

/-- Lemma B.11: compactness and coefficient continuity give one positive
state bound for all materials, admissible strains, and nonnegative times. -/
theorem prony_state_uniform_bound {n : ℕ} (P : PronyModel M E n)
    (L : Set M) (hL : IsCompact L) (hcoef : ∀ k, ContinuousOn (P.coefficient k) L)
    {βE βV δ : ℝ} (hβE : 0 < βE) (hβV : 0 < βV) (hδ : 0 < δ)
    (hRate : ∀ k, 0 < P.rate k) :
    ∃ δIV : ℝ, 0 < δIV ∧ ∀ a ∈ L, ∀ e : BoundedTrajectory E,
      e.Admissible βE βV δ → ∀ t : ℝ, 0 ≤ t → ‖P.state a e t‖ ≤ δIV := by
  classical
  choose C hC using fun k => hL.exists_bound_of_continuousOn (hcoef k)
  let s : Finset ℝ := insert 1 (Finset.univ.image P.rate)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let rateLower := s.min' hs
  have hpos : ∀ r ∈ s, 0 < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · norm_num
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hr
      exact hRate k
  have hRateLower : 0 < rateLower := hpos _ (Finset.min'_mem s hs)
  have hRate' (k : Fin n) : rateLower ≤ P.rate k :=
    Finset.min'_le s _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  let B := δ / (βV * rateLower) * Real.sqrt (∑ k : Fin n, (max (C k) 0) ^ 2)
  have hB : 0 ≤ B := mul_nonneg (div_nonneg hδ.le (mul_nonneg hβV.le hRateLower.le))
    (Real.sqrt_nonneg _)
  refine ⟨1 + B, by linarith, ?_⟩
  intro a ha e he t ht
  have hbound := prony_state_bound P a hβE hβV hδ.le hRateLower hRate'
    (fun k => max (C k) 0) (fun _ => le_max_right _ _)
    (fun k => (hC k a ha).trans (le_max_left _ _)) e he ht
  exact hbound.trans (by dsimp only [B]; linarith)

end KVApproximation.Dynamics
