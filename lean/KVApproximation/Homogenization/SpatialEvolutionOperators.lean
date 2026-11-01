module

public import KVApproximation.Homogenization.SpatialCoercivity
public import KVApproximation.Homogenization.RescaledFieldProperties
public import KVApproximation.OperatorTheory.CoerciveSolvers

/-!
# Spatial operators for microscopic evolution
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor KVApproximation.OperatorTheory

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

/-- Theorem 3.1, spatial variational operators: actual periodic
coefficient multiplication gives a coercive form on the Dirichlet space. -/
def periodicSpatialForm (A : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0) :
    CoerciveForm (ZeroBoundaryH1 Ω) where
  form := boundedSpatialForm (rescaledCoefficient Ω A.field ε hε)
  symmetric := boundedSpatialForm_symmetric _
  coercive := boundedSpatialForm_isCoercive _ hΩ A.lower_pos
    ((hasBounds_rescaledCoefficient_ae Ω A.field ε hε A.bounds).mono fun _ hx e => (hx e).1)

/-- Theorem 3.1, microscopic generator: viscosity inverse composed
with elasticity on the actual spatial Dirichlet Hilbert space. -/
def microscopicRelaxation (V E : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0) :
    ZeroBoundaryH1 Ω →L[ℝ] ZeroBoundaryH1 Ω :=
  relativeRiesz (periodicSpatialForm V hΩ ε hε) (periodicSpatialForm E hΩ ε hε)

/-- Theorem 3.1, Duhamel forcing: the viscous equilibrium map sends
an L² load to its initial displacement for the homogeneous evolution. -/
def microscopicLoadL (V : CoerciveField d)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d))) (ε : ℝ) (hε : ε ≠ 0) :
    SpatialL2 Ω →L[ℝ] ZeroBoundaryH1 Ω :=
  (periodicSpatialForm V hΩ ε hε).solveL.comp spatialLoadOperator

end KVApproximation.Homogenization
