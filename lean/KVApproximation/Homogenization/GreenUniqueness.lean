module

public import KVApproximation.Homogenization.CellConstitutive
public import KVApproximation.Homogenization.CellTensorBounds
public import KVApproximation.Homogenization.ConstantSpatialCoercivity
public import KVApproximation.Homogenization.GreenDualSpace
public import KVApproximation.Analysis.VolterraUniqueness

/-!
# Uniqueness of the homogenized Green balance
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

attribute [local instance] GreenUniqueness.instDualNormedGroup
  GreenUniqueness.instDualNormedSpace

/-- Theorem 3.1, Duhamel's formula: continuous viscously prepared
trajectories satisfying the same cell-memory Green balance agree on the
nonnegative half-line. -/
theorem green_balance_unique
    (V E : CoerciveField d) (C : CellConstitutiveModel V E)
    (hΩ : Bornology.IsBounded (Ω : Set (PhysicalSpace d)))
    (g : SpatialL2 Ω) (v w : ℝ → ZeroBoundaryH1 Ω)
    (hv : ContinuousOn v (Set.Ici (0 : ℝ)))
    (hw : ContinuousOn w (Set.Ici (0 : ℝ)))
    (hvb : ∀ t : ℝ, 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (v t) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, v r) +
        posConvolution C.kernel v (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g)
    (hwb : ∀ t : ℝ, 0 ≤ t →
      constantSpatialFormL (Ω := Ω) C.viscosity (w t) +
        constantSpatialFormL (Ω := Ω) C.elasticity (∫ r in (0 : ℝ)..t, w r) +
        posConvolution C.kernel w (constantSpatialFormL (Ω := Ω)) volume t =
          spatialLoadOperator (Ω := Ω) g) :
    Set.EqOn v w (Set.Ici (0 : ℝ)) := by
  have hV : PositiveDefinite C.viscosity := by
    refine ⟨V.lower, V.lower_pos, fun e => ?_⟩
    rw [C.viscosity_eq]
    exact (effectiveForm_bounds V V.lower_pos V.bounds e).1
  obtain ⟨c, hc, hcoercive⟩ :=
    exists_constantSpatialFormL_norm_bound (Ω := Ω) C.viscosity hV hΩ
  intro t ht
  exact (eqOn_of_integrated_memory_eq ht v w
    (hv.mono fun _ hs => hs.1) (hw.mono fun _ hs => hs.1)
    (constantSpatialFormL (Ω := Ω) C.viscosity)
    (constantSpatialFormL (Ω := Ω) C.elasticity)
    (constantSpatialFormL (Ω := Ω)) C.kernel (cellKernel_continuous V E C)
    c hc.le hcoercive
    (fun s hs => (hvb s hs.1).trans (hwb s hs.1).symm)) ⟨ht, le_rfl⟩

end KVApproximation.Homogenization
