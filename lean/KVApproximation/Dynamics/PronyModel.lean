module

public import KVApproximation.Dynamics.Trajectory
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Prony models and internal variables
-/

@[expose] public section

noncomputable section

namespace KVApproximation.Dynamics

/-- Lemmas B.11–B.13: tensorial internal variables with their Euclidean
product norm. Mandel coordinates later identify this space isometrically
with the scalar state vector. -/
abbrev BlockState (n : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin n => E)

variable (M E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition B.8 and Proposition B.10: a family of Prony models with
material-independent rates. Coefficients may have either sign. -/
structure PronyModel (n : ℕ) where
  rate : Fin n → ℝ
  coefficient : Fin n → M → E →L[ℝ] E
  viscosity : M → E →L[ℝ] E
  elasticity : M → E →L[ℝ] E

variable {M E}

/-- Definition B.8 (`eq:Kn_def`): the finite exponential memory kernel. -/
def PronyModel.kernel {n : ℕ} (P : PronyModel M E n) (a : M) (t : ℝ) : E →L[ℝ] E :=
  ∑ k : Fin n, Real.exp (-P.rate k * t) • P.coefficient k a

/-- Lemma B.12 (`lem:ua_step3_no`): the exact Prony stress response. -/
def PronyModel.stressResponse {n : ℕ} (P : PronyModel M E n) (a : M)
    (e v : E) (q : BlockState n E) : E :=
  P.viscosity a v + P.elasticity a e + ∑ k : Fin n, q k

/-- Lemma B.12 (`lem:ua_step3_no`): the exact Prony kinetic response. -/
def PronyModel.kineticResponse {n : ℕ} (P : PronyModel M E n) (a : M)
    (v : E) (q : BlockState n E) : BlockState n E :=
  WithLp.toLp 2 (fun k => P.coefficient k a v - P.rate k • q k)

variable [CompleteSpace E]

/-- Proposition B.10 (`eq:q_i_duhamel`): the zero-initial-state convolution
solution, before proving its bounded Sobolev regularity. -/
def PronyModel.state {n : ℕ} (P : PronyModel M E n) (a : M)
    (e : BoundedTrajectory E) (t : ℝ) : BlockState n E :=
  WithLp.toLp 2 (fun k => ∫ s in (0 : ℝ)..t,
    Real.exp (-P.rate k * (t - s)) • P.coefficient k a (e.velocity s))

/-- Proposition B.10 (`eq:prony_homogenized_model`): the stress along the
Prony convolution state. -/
def PronyModel.stress {n : ℕ} (P : PronyModel M E n) (a : M)
    (e : BoundedTrajectory E) (t : ℝ) : E :=
  P.stressResponse a (e.value t) (e.velocity t) (P.state a e t)

end KVApproximation.Dynamics
