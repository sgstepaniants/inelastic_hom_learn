module

public import KVApproximation.Analysis.VectorSobolev
public import KVApproximation.Analysis.PeriodicCell
public import KVApproximation.Tensor.Fields

/-!
# Weak periodic elasticity
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1: square-integrable displacement-valued loads. -/
abbrev SpatialL2 {d : ℕ} (Ω : Opens (PhysicalSpace d)) : Type :=
  Lp (PhysicalSpace d) 2 (volume.restrict (Ω : Set (PhysicalSpace d)))

/-- Theorem 3.1 (`eq:two_scale_weak_form`): the symmetric weak gradient,
with the physical-index Frobenius norm. -/
def symmetricGradient {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (u : ZeroBoundaryH1 Ω) (x : PhysicalSpace d) : Symmetric d :=
  ⟨WithLp.toLp 2 (fun ij =>
    (VectorH1.gradientEntry u.val x ij.1 ij.2 +
      VectorH1.gradientEntry u.val x ij.2 ij.1) / 2), by
    intro i j
    exact congrArg (fun z : ℝ => z / 2) (add_comm _ _)⟩

/-- Theorem 3.1 (`eq:two_scale_weak_form`): the spatial elasticity form.
Its boundedness and coercivity require the coefficient bounds and Korn's inequality. -/
def spatialForm {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (A : PhysicalSpace d → Elasticity d) (u v : ZeroBoundaryH1 Ω) : ℝ :=
  ∫ x in Ω, ⟪symmetricGradient u x, action (A x) (symmetricGradient v x)⟫_ℝ

/-- Theorem 3.1: the L² pairing of a load and a test displacement. -/
def loadPairing {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (f : SpatialL2 Ω) (v : ZeroBoundaryH1 Ω) : ℝ :=
  ∫ x in Ω, ⟪f x, VectorH1.value v.val x⟫_ℝ

/-- Theorem 3.1, admissible initial conditions: elastic equilibrium with
the same fixed load for every positive microscopic scale. -/
def IsPreparedInitialFamily {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    (E : CoerciveField d) (g₀ : SpatialL2 Ω) (u₀ : ℝ → ZeroBoundaryH1 Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ v : ZeroBoundaryH1 Ω,
    spatialForm (rescalePeriodic E.field ε) (u₀ ε) v = loadPairing g₀ v

end KVApproximation.Homogenization
