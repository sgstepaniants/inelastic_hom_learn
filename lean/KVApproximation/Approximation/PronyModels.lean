module

public import KVApproximation.Approximation.LogProny
public import KVApproximation.Dynamics.PronyModel
public import KVApproximation.Tensor.Multiplication

/-!
# Internal-variable models of the spectral discretization
-/

@[expose] public section

noncomputable section

open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Definition B.8 and Proposition B.10: flatten the patch and node indices
to the `J*m` tensorial internal variables. The rates are shared by all materials. -/
def localPronyModel {M : Type*} {d : ℕ} (ν : M → TensorMeasure d)
    (Vhom Ehom : M → Elasticity d) (c lower upper : ℝ) (m : ℕ) :
    PronyModel M (Symmetric d) (logPartitionCount (logarithmicSpan lower upper) * m) where
  rate k :=
    let ji : Fin (logPartitionCount (logarithmicSpan lower upper)) × Fin m :=
      finProdFinEquiv.symm k
    localPronyRate lower upper m ji.1 ji.2
  coefficient k a :=
    let ji : Fin (logPartitionCount (logarithmicSpan lower upper)) × Fin m :=
      finProdFinEquiv.symm k
    actionL d (localPronyCoefficient (ν a) c lower upper m ji.1 ji.2)
  viscosity a := actionL d (Vhom a)
  elasticity a := actionL d (Ehom a)

/-- Definition B.8 (`eq:Ki_def_degenerate`): one tensorial internal variable
for a singleton interval. Its exactness is proved from the spectral support. -/
def singletonPronyModel {M : Type*} {d : ℕ} (ν : M → TensorMeasure d)
    (Vhom Ehom : M → Elasticity d) (rate : ℝ) : PronyModel M (Symmetric d) 1 where
  rate _ := rate
  coefficient _ a := actionL d (singletonPronyCoefficient (ν a))
  viscosity a := actionL d (Vhom a)
  elasticity a := actionL d (Ehom a)

end KVApproximation.Approximation
