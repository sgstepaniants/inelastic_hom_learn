module

public import KVApproximation.Tensor.Action
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Finite tensor-valued spectral measures
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace
open KVApproximation.Tensor

namespace KVApproximation.Spectral

/-- Proposition 3.3: countably additive elasticity-tensor-valued Borel measures. -/
abbrev TensorMeasure (d : ℕ) := VectorMeasure ℝ (Elasticity d)

/-- Proposition 3.3 (`eq:nu_def`): positive semidefiniteness on Borel sets. -/
def TensorMeasure.Positive {d : ℕ} (ν : TensorMeasure d) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B → ∀ e : Symmetric d,
    0 ≤ ⟪e, action (ν B) e⟫_ℝ

/-- Proposition 3.3: the measure vanishes off the stated spectral interval. -/
def TensorMeasure.SupportedOn {d : ℕ} (ν : TensorMeasure d) (I : Set ℝ) : Prop :=
  ν.variation Iᶜ = 0

/-- Proposition 3.3 (`eq:K_laplace`): integration of a scalar function
against a tensor-valued measure. The bilinear pairing is scalar multiplication. -/
def tensorIntegral {d : ℕ} (ν : TensorMeasure d) (f : ℝ → ℝ) : Elasticity d :=
  VectorMeasure.integral ν f (ContinuousLinearMap.lsmul ℝ ℝ (E := Elasticity d))

/-- Proposition 3.3 (`eq:tv_norm_def`): Frobenius total variation on a
Borel set, retained as an extended nonnegative real until finiteness is proved. -/
def totalVariation {d : ℕ} (ν : TensorMeasure d) (I : Set ℝ) : ENNReal :=
  ν.variation I

/-- Proposition 3.3: finite positive spectral data representing a kernel
on the nonnegative time axis. -/
def IsSpectralRepresentation {d : ℕ} (ν : TensorMeasure d)
    (K : ℝ → Elasticity d) (lower upper : ℝ) : Prop :=
  ν.Positive ∧ ν.SupportedOn (Set.Icc lower upper) ∧
    totalVariation ν Set.univ < ⊤ ∧
      ∀ t : ℝ, 0 ≤ t → K t = tensorIntegral ν (fun r => r * Real.exp (-r * t))

/-- Lemma B.6 (`eq:weighted_measure_def`): the resolvent weight. -/
def resolventWeight (c r : ℝ) : ℝ := r / (c + r)

/-- Lemma B.6: the weighted spectral measure, defined by vector-measure
integration. Its use on positive compact spectral intervals includes the
integrability proof for the resolvent weight. -/
def weightedMeasure {d : ℕ} (c : ℝ) (ν : TensorMeasure d) : TensorMeasure d :=
  ν.withDensity (resolventWeight c)
    (ContinuousLinearMap.lsmul ℝ ℝ (E := Elasticity d))

end KVApproximation.Spectral
