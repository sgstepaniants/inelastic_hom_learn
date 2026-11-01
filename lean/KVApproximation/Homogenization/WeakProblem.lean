module

public import KVApproximation.Homogenization.StaticWeakProblem
public import KVApproximation.Analysis.TimeSobolev
public import KVApproximation.Analysis.LipschitzDomain

/-!
# Weak periodic elasticity and viscoelastic evolution
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

/-- Theorem 3.1: forcing in `L²((0,T);L²(Ω;ℝᵈ))`. -/
abbrev Forcing {d : ℕ} (Ω : Opens (PhysicalSpace d)) (T : ℝ) : Type :=
  Lp (SpatialL2 Ω) 2 (volume.restrict (Set.Ioo 0 T))

/-- Theorem 3.1 (`eq:two_scale_weak_form`): the microscopic weak solution,
with its H¹₀-valued initial trace and a common exceptional time-null set. -/
def IsMicroscopicSolution {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    {T : ℝ} (hT : 0 < T) (V E : CoerciveField d) (ε : ℝ)
    (u₀ : ZeroBoundaryH1 Ω) (f : Forcing Ω T)
    (u : TimeH1 (ZeroBoundaryH1 Ω) T) : Prop :=
  Eq (α := ZeroBoundaryH1 Ω) (TimeH1.initial (H := ZeroBoundaryH1 Ω) hT u) u₀ ∧
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (rescalePeriodic V.field ε)
          (TimeH1.velocity (H := ZeroBoundaryH1 Ω) u t) v +
        spatialForm (rescalePeriodic E.field ε)
          (TimeH1.value (H := ZeroBoundaryH1 Ω) u t) v =
          loadPairing (f t) v

/-- Theorem 3.1 (`eq:homogenized_model_identified`): weak balance with
the memory convolution, and the elastically prepared homogenized initial
condition. The cell construction supplies the tensors and kernel. -/
def IsHomogenizedSolution {d : ℕ} {Ω : Opens (PhysicalSpace d)}
    {T : ℝ} (hT : 0 < T) (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d)
    (g₀ : SpatialL2 Ω) (f : Forcing Ω T)
    (u : TimeH1 (ZeroBoundaryH1 Ω) T) : Prop :=
  (∀ v : ZeroBoundaryH1 Ω,
    spatialForm (fun _ => Ehom)
      (TimeH1.initial (H := ZeroBoundaryH1 Ω) hT u) v =
        loadPairing g₀ v) ∧
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : ZeroBoundaryH1 Ω,
      spatialForm (fun _ => Vhom) (TimeH1.velocity (H := ZeroBoundaryH1 Ω) u t) v +
        spatialForm (fun _ => Ehom) (TimeH1.value (H := ZeroBoundaryH1 Ω) u t) v +
        (∫ s in (0 : ℝ)..t,
          spatialForm (fun _ => K (t - s))
            (TimeH1.velocity (H := ZeroBoundaryH1 Ω) u s) v) =
          loadPairing (f t) v

end KVApproximation.Homogenization
