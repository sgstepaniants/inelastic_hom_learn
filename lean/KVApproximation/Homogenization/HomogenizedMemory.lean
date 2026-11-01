module

public import KVApproximation.Homogenization.ConstantSpatialFormProperties
public import KVApproximation.Homogenization.SpatialFormIdentities
public import KVApproximation.Homogenization.WeakProblem
public import KVApproximation.Analysis.TimeSobolevProperties
public import KVApproximation.Analysis.CausalConvolution

/-!
# The homogenized equation in the spatial dual

Continuous spatial forms identify the tested weak equation with one
dual-valued equation, including the prepared initial condition.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open KVApproximation.Analysis KVApproximation.Tensor

namespace KVApproximation.Homogenization

variable {d : ℕ} {Ω : Opens (PhysicalSpace d)}

local instance HomogenizedMemory.instNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedMemory.instNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω) := inferInstance

local instance HomogenizedMemory.instDualNormedGroup :
    NormedAddCommGroup (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance HomogenizedMemory.instDualNormedSpace :
    NormedSpace ℝ (ZeroBoundaryH1 Ω →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Theorem 3.1 (`eq:homogenized_model_identified`): the actual spatial
weak formulation is the dual-valued memory equation, with its prepared
initial condition and one common exceptional time-null set. -/
theorem isHomogenizedSolution_iff_memory_equation {T : ℝ} (hT : 0 < T)
    (Vhom Ehom : Elasticity d) (K : ℝ → Elasticity d) (hK : Continuous K)
    (g₀ : SpatialL2 Ω) (f : Forcing Ω T) (u : TimeH1 (ZeroBoundaryH1 Ω) T) :
    IsHomogenizedSolution hT Vhom Ehom K g₀ f u ↔
      constantSpatialFormL (Ω := Ω) Ehom (TimeH1.initial hT u) =
          spatialLoadOperator (Ω := Ω) g₀ ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
          constantSpatialFormL (Ω := Ω) Vhom (TimeH1.velocity u t) +
            constantSpatialFormL (Ω := Ω) Ehom (TimeH1.value u t) +
            posConvolution K (TimeH1.velocity u) (constantSpatialFormL (Ω := Ω)) volume t =
              spatialLoadOperator (Ω := Ω) (f t) := by
  have hvel : IntervalIntegrable (TimeH1.velocity u) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2
      ((TimeH1.velocity_memLp u).integrable (by norm_num))
  have hmemory (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (w : ZeroBoundaryH1 Ω) :
      (posConvolution K (TimeH1.velocity u) (constantSpatialFormL (Ω := Ω)) volume t) w =
        ∫ r in (0 : ℝ)..t,
          spatialForm (fun _ => K (t - r)) (TimeH1.velocity u r) w := by
    rw [posConvolution_eq_integral_sub (constantSpatialFormL (Ω := Ω)) K _ ht.1,
      ContinuousLinearMap.intervalIntegral_apply
        (intervalIntegrable_posConvolution_integrand (constantSpatialFormL (Ω := Ω))
          K (TimeH1.velocity u) hK hvel ht) w]
    apply intervalIntegral.integral_congr
    intro r _
    exact constantSpatialFormL_apply (K (t - r)) (TimeH1.velocity u r) w
  constructor
  · rintro ⟨hinit, hode⟩
    refine ⟨?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro w
      simpa only [constantSpatialFormL_apply, spatialLoadOperator_apply] using hinit w
    · filter_upwards [hode, ae_restrict_mem measurableSet_Ioo] with t ht htm
      apply ContinuousLinearMap.ext
      intro w
      simpa only [add_apply, constantSpatialFormL_apply,
        hmemory t ⟨htm.1.le, htm.2.le⟩ w, spatialLoadOperator_apply] using ht w
  · rintro ⟨hinit, hode⟩
    refine ⟨?_, ?_⟩
    · intro w
      have h := congrArg (fun ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ => ℓ w) hinit
      simpa only [constantSpatialFormL_apply, spatialLoadOperator_apply] using h
    · filter_upwards [hode, ae_restrict_mem measurableSet_Ioo] with t ht htm
      intro w
      have h := congrArg (fun ℓ : ZeroBoundaryH1 Ω →L[ℝ] ℝ => ℓ w) ht
      simpa only [add_apply, constantSpatialFormL_apply,
        hmemory t ⟨htm.1.le, htm.2.le⟩ w, spatialLoadOperator_apply] using h

end KVApproximation.Homogenization
