module

public import KVApproximation.Approximation.PronyModels
public import KVApproximation.Approximation.AlternativeDimension

/-!
# Alternative Prony constructions
-/

@[expose] public section

noncomputable section

open KVApproximation.Tensor KVApproximation.Spectral KVApproximation.Dynamics

namespace KVApproximation.Approximation

/-- Remark 4.6 (`rmk:prony_construction_choices`): local interpolation
without reweighting, with the rate included in each coefficient. -/
def unweightedLocalCoefficient {d : ℕ} (ν : TensorMeasure d) (lower upper : ℝ) (m : ℕ)
    (j : Fin (logPartitionCount (logarithmicSpan lower upper))) (i : Fin m) : Elasticity d :=
  localPronyRate lower upper m j i • tensorIntegral ν (fun r =>
    spectralWeight lower upper j r *
      (chebyshevLagrange m i).eval (localCoordinate lower (logarithmicSpan lower upper) j r))

/-- Remark 4.6: the unweighted local Prony model with the same shared rates. -/
def unweightedLocalModel {M : Type*} {d : ℕ} (ν : M → TensorMeasure d)
    (Vhom Ehom : M → Elasticity d) (lower upper : ℝ) (m : ℕ) :
    PronyModel M (Symmetric d) (logPartitionCount (logarithmicSpan lower upper) * m) where
  rate k :=
    let ji : Fin (logPartitionCount (logarithmicSpan lower upper)) × Fin m := finProdFinEquiv.symm k
    localPronyRate lower upper m ji.1 ji.2
  coefficient k a :=
    let ji : Fin (logPartitionCount (logarithmicSpan lower upper)) × Fin m := finProdFinEquiv.symm k
    actionL d (unweightedLocalCoefficient (ν a) lower upper m ji.1 ji.2)
  viscosity a := actionL d (Vhom a)
  elasticity a := actionL d (Ehom a)

/-- Remark 4.6: the reference-to-rate map for one interpolant over the
entire logarithmic interval. -/
def globalLogRate (lower upper x : ℝ) : ℝ :=
  lower * Real.exp (logarithmicSpan lower upper / 2 * (1 + x))

/-- Remark 4.6: the inverse reference coordinate for the global interpolant. -/
def globalLogCoordinate (lower upper r : ℝ) : ℝ :=
  2 * Real.log (r / lower) / logarithmicSpan lower upper - 1

/-- Remark 4.6: weighted coefficients for a single logarithmic interpolant. -/
def globalPronyCoefficient {d : ℕ} (ν : TensorMeasure d) (c lower upper : ℝ)
    (n : ℕ) (i : Fin n) : Elasticity d :=
  (c + globalLogRate lower upper (chebyshevNode n i)) •
    tensorIntegral (weightedMeasure c ν)
      (fun r => (chebyshevLagrange n i).eval (globalLogCoordinate lower upper r))

/-- Remark 4.6: the weighted Prony model from a single global interpolant. -/
def globalPronyModel {M : Type*} {d : ℕ} (ν : M → TensorMeasure d)
    (Vhom Ehom : M → Elasticity d) (c lower upper : ℝ) (n : ℕ) :
    PronyModel M (Symmetric d) n where
  rate i := globalLogRate lower upper (chebyshevNode n i)
  coefficient i a := actionL d (globalPronyCoefficient (ν a) c lower upper n i)
  viscosity a := actionL d (Vhom a)
  elasticity a := actionL d (Ehom a)


end KVApproximation.Approximation
