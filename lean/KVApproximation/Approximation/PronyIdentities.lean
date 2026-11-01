module

public import KVApproximation.Approximation.PronyModels
public import KVApproximation.Approximation.SpectralPartition
public import KVApproximation.Approximation.ChebyshevNodes

/-!
# Rates and finite sums in the Prony construction
-/

public section

open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Definition B.8: all local rates belong to the common spectral interval. -/
theorem localPronyRate_mem {lower upper : ℝ} (hlower : 0 < lower) (horder : lower < upper)
    {m : ℕ} (_hm : 0 < m)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (i : Fin m) :
    localPronyRate lower upper m j i ∈ Set.Icc lower upper :=
  localRate_mem_interval hlower horder j (chebyshevNode_mem m i)

/-- Definition B.8 (`eq:Kn_def`): flattening the local indices preserves
the exact tensor-valued kernel. -/
theorem localPronyModel_kernel {M : Type*} {d : ℕ} (ν : M → TensorMeasure d)
    (Vhom Ehom : M → Elasticity d) (c lower upper : ℝ) (m : ℕ) (a : M) (t : ℝ) :
    (localPronyModel ν Vhom Ehom c lower upper m).kernel a t =
      actionL d (localPronyKernel (ν a) c lower upper m t) := by
  unfold PronyModel.kernel localPronyModel localPronyKernel
  simp only [map_sum, map_smul]
  exact (Fintype.sum_equiv finProdFinEquiv.symm _
    (fun ji => Real.exp (-localPronyRate lower upper m ji.1 ji.2 * t) •
      actionL d (localPronyCoefficient (ν a) c lower upper m ji.1 ji.2))
    (fun _ => rfl)).trans (Fintype.sum_prod_type _)

end KVApproximation.Approximation
