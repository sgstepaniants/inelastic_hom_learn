module

public import KVApproximation.Approximation.PartitionResponse
public import KVApproximation.Approximation.PronyModels
public import KVApproximation.Spectral.TensorActionIntegral

/-!
# Spectral and Prony memory representations
-/

public section

open KVApproximation.Dynamics KVApproximation.Tensor KVApproximation.Spectral

namespace KVApproximation.Approximation

/-- Proposition B.10, proof: the exact memory convolution is integration
of the real weighted response against the resolvent-weighted measure. -/
theorem memory_eq_weightedResponseIntegral {d : ℕ} {lower upper c : ℝ}
    (hlower : 0 < lower) (hc : 0 < c) (ν : TensorMeasure d)
    (K : ℝ → Elasticity d) (hrep : IsSpectralRepresentation ν K lower upper)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, action (K (t - s)) (e.velocity s)) =
      tensorActionIntegral (weightedMeasure c ν) (realWeightedResponse c e t) := by
  sorry

/-- Proposition B.10, coefficient assembly: the finite Prony stress is
the instantaneous response plus the integrated partitioned interpolant. -/
theorem local_prony_stress_eq_partitionIntegral {M : Type*} {d : ℕ}
    (ν : M → TensorMeasure d) (Vhom Ehom : M → Elasticity d)
    {c lower upper : ℝ} (hlower : 0 < lower) (hc : 0 < c) (m : ℕ) (a : M)
    (hνpos : (ν a).Positive) (hνsupport : (ν a).SupportedOn (Set.Icc lower upper))
    (hνfinite : totalVariation (ν a) Set.univ < ⊤)
    (e : BoundedTrajectory (Symmetric d)) {t : ℝ} (ht : 0 ≤ t) :
    (localPronyModel ν Vhom Ehom c lower upper m).stress a e t =
      action (Vhom a) (e.velocity t) + action (Ehom a) (e.value t) +
        tensorActionIntegral (weightedMeasure c (ν a))
          (partitionResponse c lower upper m e t) := by
  sorry

end KVApproximation.Approximation
