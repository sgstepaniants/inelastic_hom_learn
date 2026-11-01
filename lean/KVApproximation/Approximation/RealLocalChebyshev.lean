import KVApproximation.Approximation.RealResponseIdentities
import KVApproximation.Approximation.LocalChebyshev

/-!
# Real local interpolation error
-/

open KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Proposition B.10, applying Lemma B.9: the real local interpolant has
the exact same error as its complexified counterpart, including one node. -/
theorem real_local_response_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : BoundedTrajectory E) {βE βV δ lower R t : ℝ}
    (hβE : 0 < βE) (hβV : 0 < βV) (he : e.Admissible βE βV δ)
    (hlower : 0 < lower) (hR : 0 < R) (ht : 0 ≤ t)
    {m : ℕ} (hm : 1 ≤ m) (j : Fin (logPartitionCount R))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖realWeightedResponse (βE / βV) e t (localRate lower R j x) -
      realLocalResponseInterpolant (βE / βV) lower R m j e t x‖ ≤
      localResponseErrorBound δ βV m := by
  let J := TauCeti.Complexification.ofRealLI E
  have hmap (y : ℝ) :
      J (realWeightedResponse (βE / βV) e t (localRate lower R j y)) =
        localWeightedResponse J.toContinuousLinearMap (βE / βV) lower R j e t y := by
    rw [localWeightedResponse, complexLocalRate_ofReal]
    exact map_realWeightedResponse J.toContinuousLinearMap _ e ht _
  have hpoly : J (realLocalResponseInterpolant (βE / βV) lower R m j e t x) =
      chebyshevInterpolant m
        (localWeightedResponse J.toContinuousLinearMap (βE / βV) lower R j e t) x := by
    simp only [realLocalResponseInterpolant, chebyshevInterpolant, map_sum, map_smul,
      hmap, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have h := local_weighted_response_error J e hβE hβV he hlower hR ht hm j hx
  rw [← hmap x, ← hpoly, ← J.map_sub, J.norm_map] at h
  exact h

end KVApproximation.Approximation
